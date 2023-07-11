theory "Semi-Topology"
  imports Main
begin

text \<open>
This is a formalisation of a few notions of semitopology and related lemmas,
following @{url "https://arxiv.org/abs/2303.09287"}
\<close>

text \<open>
In general we try to use to decompose proof into readable steps which are each discharged
automatically using Sledgehammer (which automatically inserts the lines starting with \<open>by\<close>)
\<close>

no_notation
  \<comment> \<open>The default meaning of @{term "O"} (relation composition) is annoying so we remove it\<close>
  relcomp (infixr "O" 75)

section "Definition of a semitopology"

locale semitopology =
  fixes "open" :: "'a set \<Rightarrow> bool"
  assumes "\<And> Os . \<forall> O \<in> Os . open O \<Longrightarrow> open (\<Union> Os)"
    and "open UNIV"
begin

lemma "open {}"
  \<comment> \<open>The axioms imply that the empty set is open\<close>
  by (metis Sup_empty empty_iff semitopology_axioms semitopology_def)

section "Section 2"

lemma l_2_3_2:
  \<comment> \<open>If every member of @{term S} has an open neighborhood in @{term S}, then @{term S} is open.\<close>
  fixes S
  shows "(\<forall> p \<in> S . \<exists> O . open O \<and> p \<in> O \<and> O \<subseteq> S) \<longleftrightarrow> open S"
proof -
  have "open S" if "\<forall> p \<in> S . \<exists> O . open O \<and> p \<in> O \<and> O \<subseteq> S"
  proof -
    from \<open>\<forall> p \<in> S . \<exists> O . open O \<and> p \<in> O \<and> O \<subseteq> S\<close>
    obtain f where 1:"\<forall> p \<in> S . open (f p) \<and> p \<in> f p \<and> f p \<subseteq> S" 
      \<comment> \<open>first we skolemize the existential in the assumption\<close>
      by metis
    from 1 have 2:"S = \<Union> {f p | p . p \<in> S}" by blast
    from 1 have 3:"open (f p)" if "p \<in> S" for p using `p\<in>S` by auto
    from 2 3 show ?thesis
      by (smt (verit, ccfv_SIG) mem_Collect_eq semitopology_axioms semitopology_def)
  qed
  moreover
  have "\<forall> p \<in> S . \<exists> O . open O \<and> p \<in> O \<and> O \<subseteq> S" if "open S"
    using that by blast
  ultimately show ?thesis by blast
qed

section "Section 3"

subsection "Subsection 3.1"

definition intersects :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "int" 100)
  where "intersects a b \<equiv> a \<inter> b \<noteq> {}"

lemma int_commutes:
  fixes S S'
  shows "S int S' = S' int S"
  by (simp add: inf_commute intersects_def)

lemma int_refl:
  fixes S
  shows "S int S = (S \<noteq> {})"
  by (simp add: local.intersects_def)

lemma int_union:
  fixes X Y Z
  shows "X int (Y \<union> Z) = (X int Y \<or> X int Z)"
  by (simp add: Int_Un_distrib local.intersects_def)

lemma subset_int:
  fixes X X'
  assumes "X \<subseteq> X'" and "X\<noteq>{}"
  shows "X int X'"
  by (metis assms inf.orderE local.intersects_def)

lemma subset_int_other_1:
  fixes X X' Y
  assumes "X \<subseteq> X'" and "X int Y"
  shows "X' int Y"
  by (metis assms int_commutes int_union subset_Un_eq)

lemma subset_int_other_2:
  fixes X X' Y
  assumes "Y \<subseteq> Y'" and "X int Y"
  shows "X int Y'"
  by (metis assms int_union subset_Un_eq)

definition transitive
  where "transitive S \<equiv> \<forall> O O' . open O \<and> open O' \<and> S int O \<and> S int O' \<longrightarrow> O int O'"

definition topen
  where "topen S \<equiv> S \<noteq> {} \<and> open S \<and> transitive S"

subsection "Subsection 3.4"

lemma l_3_4_2_1:
  fixes S S'
  assumes "S' \<subseteq> S" and "transitive S"
  shows "transitive S'"
  by (metis Int_assoc Int_empty_right assms le_iff_inf local.intersects_def local.transitive_def)

lemma l_3_4_2_2:
  fixes S S'
  assumes "S' \<subseteq> S" and "topen S" and "S' \<noteq> {}" and "open S'"
  shows "topen S'"
  using assms l_3_4_2_1 topen_def by force

lemma l_3_4_3_1:
  fixes S S' O O'
  assumes "transitive S" and "transitive S'" and "open S \<or> open S'"
  and "open O" and "open O'" and "O int S" and "S int S'" and "S' int O'"
  shows "O int O'"
  by (metis Int_commute assms local.intersects_def local.transitive_def) 

lemma l_3_4_3_2:
  fixes S S'
  assumes "S int S'" and "transitive S" and "transitive S'" and "open S \<or> open S'"
  shows "transitive (S \<union> S')"
  by (smt (verit) Un_iff assms disjoint_iff_not_equal local.intersects_def local.transitive_def)

subsection "Subsection 3.5"

definition connected where
  "connected Ss \<equiv> \<forall> S \<in> Ss . \<forall> S' \<in> Ss . S int S'"

lemma l_3_5_2_1:
  fixes S S'
  assumes "S int S'" and "topen S" and "topen S'"
  shows "topen (S \<union> S')"
  by (metis Un_empty Un_iff Un_upper1 Un_upper2 assms l_2_3_2 l_3_4_3_2 semitopology.topen_def semitopology_axioms)

subsection "Subsection 3.6"

definition intertwined where
  "intertwined p p' == transitive {p, p'}"

lemma def_3_6_1:
  fixes p p'
  shows  "intertwined p p' = (\<forall> O O' . open O \<and> open O' \<and> p \<in> O \<and> p' \<in> O' \<longrightarrow> O int O')"
proof -
  have "intertwined p p'" if "\<forall> O O' . open O \<and> open O' \<and> p \<in> O \<and> p' \<in> O' \<longrightarrow> O int O'"
    by (smt (verit, best) Int_commute inf_right_idem insert_absorb insert_disjoint(2) intersects_def intertwined_def that transitive_def)
  moreover
  have "\<forall> O O' . open O \<and> open O' \<and> p \<in> O \<and> p' \<in> O' \<longrightarrow> O int O'" if "intertwined p p'"
    using intersects_def intertwined_def that transitive_def by auto
  ultimately show ?thesis by auto
qed

lemma l_3_6_4_a:
  fixes S
  shows "transitive S = (\<forall> p \<in> S . \<forall> p' \<in> S . intertwined p p')"
proof
  show "\<forall> p \<in> S . \<forall> p' \<in> S . intertwined p p'" if "transitive S"
    by (simp add: intertwined_def l_3_4_2_1 that)
  show "transitive S" if "\<forall> p \<in> S . \<forall> p' \<in> S . intertwined p p'"
    by (smt (verit, best) that disjoint_iff_not_equal def_3_6_1 semitopology.intersects_def semitopology.transitive_def semitopology_axioms)
qed

lemma l_3_6_4_b:
  fixes S
  shows "transitive S = (\<forall> p \<in> S . \<forall> p' \<in> S . transitive {p, p'})"
  using intertwined_def l_3_6_4_a by auto

section "Section 4"

definition interior where
  "interior R \<equiv> \<Union> {O . open O \<and> O \<subseteq> R}"

subsection "Subsection 4.4"

definition K where
  \<comment> \<open>The community of a point\<close>
  "K p \<equiv> interior {p' . intertwined p p'}"

definition regular where
  "regular p \<equiv> p \<in> K p  \<and>  topen(K p)"

lemma interior_open:
  fixes R
  shows "open (interior R)"
proof -
  have "\<exists> O . open O \<and> O \<subseteq> interior R \<and> p \<in> O" if "p \<in> interior R" for p
    using interior_def that by auto
  thus ?thesis
    by (meson l_2_3_2)
qed

section "Section 5"

subsection "Subsection 5.1"

definition closure where
  "closure R \<equiv> {p . \<forall> O . open O \<and> p \<in> O \<longrightarrow> O int R}"

lemma closure_monotone:
  fixes R R'
  assumes "R \<subseteq> R'"
  shows "closure R \<subseteq> closure R'"
  using assms closure_def subset_int_other_2 by force

lemma closure_increasing:
  fixes R
  shows "R \<subseteq> closure R"
  using closure_def local.intersects_def by auto

lemma closure_idempotent:
  fixes R
  shows "closure R = closure (closure R)"
proof
  show "closure R \<subseteq> closure (closure R)"
    by (simp add: closure_increasing)
next
  show "closure (closure R) \<subseteq> closure R"
  proof -
    { fix p
      assume "p \<in> closure (closure R)" and "p \<notin> closure R"
      hence False
        unfolding closure_def intersects_def by auto }
    thus ?thesis
      by blast
  qed
qed

definition closed where
  "closed R \<equiv> R = closure R"

definition clopen where
  "clopen R \<equiv> open R \<and> closed R"

lemma complement_closed_is_open:
  fixes R
  assumes "closed R"
  shows "open (- R)"
proof -
  have "\<exists> O . open O \<and> O \<subseteq> - R \<and> p \<in> O" if "p \<in> -R" for p
  proof -
    from `p \<in> - R`
    have "p \<in> - (closure R)"
      using assms closed_def by auto
    hence "\<exists> O . open O \<and> O \<inter> R = {} \<and> p \<in> O"
      using closure_def local.intersects_def by auto
    thus ?thesis
      by (simp add: inf_shunt)
  qed
  thus ?thesis
    by (meson l_2_3_2) 
qed

lemma complement_open_is_closed:
  fixes O
  assumes "open O"
  shows "closed (-O)"
proof -
  have "O \<inter> closure (-O) = {}"
    using assms closure_def semitopology.intersects_def semitopology_axioms by fastforce
  thus ?thesis
    by (meson closed_def closure_increasing compl_le_swap1 disjoint_eq_subset_Compl subset_antisym)
qed

lemma empty_closed:
  "closed {}"
  by (metis Compl_UNIV_eq complement_open_is_closed semitopology_axioms semitopology_def)

lemma univ_closed: "closed UNIV"
  using closed_def closure_increasing by blast

lemma intersection_of_closed_is_closed:
  fixes Rs
  assumes "\<forall> R \<in> Rs . closed R"
  shows "closed (\<Inter> Rs)"
proof -
  have 1:"\<Inter>Rs = -\<Union>{-R | R . R \<in> Rs}"
    by (simp add: Setcompr_eq_image)
  thus ?thesis
    by (smt (verit, del_insts) assms complement_closed_is_open complement_open_is_closed mem_Collect_eq semitopology_axioms semitopology_def)
qed

lemma closure_as_intersection:
  fixes R
  shows "closure R = \<Inter> {C . closed C \<and> R \<subseteq> C}"
  by (smt (z3) cInf_eq_minimum closure_idempotent closure_increasing closure_monotone mem_Collect_eq semitopology.closed_def semitopology_axioms) 

lemma interior_of_closed_in_closed:
  fixes C
  assumes "closed C"
  shows "interior C \<subseteq> C"
    using semitopology.interior_def semitopology_axioms by auto

lemma open_in_interior_of_closure:
  fixes O
  assumes "open O"
  shows "O \<subseteq> interior (closure O)"
  using assms closure_increasing interior_def by auto

lemma closure_of_interior_of_closed_in_closed:
  fixes C
  assumes "closed C"
  shows "closure (interior C) \<subseteq> C"
  by (metis assms closed_def closure_monotone interior_of_closed_in_closed)

subsection "Subsection 5.3"

lemma intertwined_iff_in_closure_of_neighbourhood:
  fixes p p'
  shows "intertwined p p' = (\<forall> O . open O \<and> p \<in> O \<longrightarrow> p' \<in> closure O)"
  using closure_def semitopology.int_commutes def_3_6_1 semitopology_axioms by fastforce

lemma intertwined_is_intersection_of_closures_of_neighbourhoods:
  fixes p
  shows "{p' . intertwined p p'} = \<Inter> {closure O | O . open O \<and> p \<in> O}"
proof -
  have "\<Inter> {closure O | O . open O \<and> p \<in> O} = {p' . \<forall> O . open O \<and> p\<in>O \<longrightarrow> p' \<in> closure O}"
    by auto
  thus ?thesis
    by (simp add: semitopology.intertwined_iff_in_closure_of_neighbourhood semitopology_axioms)
qed

lemma intertwined_is_intersection_of_closed:
  fixes p
  shows "{p' . intertwined p p'} = \<Inter> {C . closed C \<and> p \<in> interior C}"
proof -
  have "\<Inter> {closure O | O . open O \<and> p \<in> O} = \<Inter> {C . closed C \<and> p \<in> interior C}"
  proof -
    have "\<exists> C . closed C \<and> p \<in> interior C \<and> C \<subseteq> closure O" if "open O" and "p \<in> O" for O
    proof -
      define C where "C \<equiv> closure O"
      have "closed C"
        using C_def closed_def closure_idempotent by auto
      moreover have "C \<subseteq> closure O"
        by (simp add: C_def)
      moreover have "p \<in> interior C"
        using C_def open_in_interior_of_closure that by blast
      ultimately show ?thesis
        by blast
    qed
    hence "\<Inter> {C . closed C \<and> p \<in> interior C} \<subseteq> \<Inter> {closure O | O . open O \<and> p \<in> O}"
      by fastforce
    moreover
    have "\<exists> O . open O \<and> p \<in> O \<and> closure O \<subseteq> C" if "closed C" and "p \<in> interior C" for C
    proof -
      define O where "O \<equiv> interior C"
      have "open O"
        by (simp add: O_def interior_open)
      moreover have "p \<in> O"
        using O_def that(2) by auto
      moreover have "closure O \<subseteq> C"
        by (simp add: O_def closure_of_interior_of_closed_in_closed that(1))
      ultimately show ?thesis by blast
    qed
    hence "\<Inter> {closure O | O . open O \<and> p \<in> O} \<subseteq> \<Inter> {C . closed C \<and> p \<in> interior C}" 
      by fastforce
    ultimately
    show ?thesis by auto
  qed
  thus ?thesis
    by (simp add: semitopology.intertwined_is_intersection_of_closures_of_neighbourhoods semitopology_axioms)
qed

lemma "closed {p' . intertwined p p'}"
  using intersection_of_closed_is_closed intertwined_is_intersection_of_closed by auto

lemma closure_in_intertwined_set:
  "closure {p} \<subseteq> {p' . intertwined p p'}"
  by (smt (verit) closure_def insert_is_Un int_commutes int_union mem_Collect_eq mk_disjoint_insert
      semitopology.def_3_6_1 semitopology_axioms subsetI)

lemma closure_is_intertwined_set:
  assumes "interior (closure {p}) \<noteq> {}"
  shows "closure {p} = {p' . intertwined p p'}"
  oops

lemma cascade:
  \<comment> \<open>This is a version of the Cascade Theorem\<close>
  fixes S O
  assumes "topen S" and "open O" and "O int S"
  shows "S \<subseteq> closure O" using closure_increasing
  by (smt (verit, best) assms int_commutes closure_def mem_Collect_eq semitopology.topen_def semitopology_axioms subsetD subsetI transitive_def)


section "Appendix B.2"

lemma l_b_2_1:
  fixes p p'
  shows "intertwined p p' = 
    (\<forall> C C' . closed C \<and> closed C' \<and> C \<union> C' = UNIV \<longrightarrow> {p,p'} \<subseteq> C \<or> {p,p'} \<subseteq> C')"
proof -
  have "intertwined p p' = 
    (\<forall> C C' . closed C \<and> closed C' \<and> p \<notin> C \<and> p' \<notin> C' \<longrightarrow> C \<union> C' \<noteq> UNIV)"
  proof -
    { fix C C'
      assume "intertwined p p'" and "closed C" and "closed C'"
        and "p \<notin> C" and "p' \<notin> C'"
      have "C \<union> C' \<noteq> UNIV"
      proof -
        \<comment> \<open>If @{term "C \<union> C' = UNIV"} were the case, then @{term "p \<in> -C'"} and @{term "p' \<in> -C"}.
            However both are open and disjoint, thus @{term p} and @{term p'} cannot be intertwined.\<close>
        { assume "C \<union> C' = UNIV"
          have "open (-C)" and "open (-C')" 
            using \<open>closed C\<close> and \<open>closed C'\<close> complement_closed_is_open by auto
          moreover have "p \<in> -C" and "p' \<in> -C'"
            using \<open>p \<notin> C\<close> and \<open>p' \<notin> C'\<close> by auto
          moreover have "-C \<inter> -C' = {}"
            using \<open>C \<union> C' = UNIV\<close>
            by auto
          ultimately
          have False
            using \<open>intertwined p p'\<close> def_3_6_1 intersects_def by fastforce }
        thus ?thesis
          by auto
      qed }
    moreover
    { assume a0:"closed C \<and> closed C' \<and> p \<notin> C \<and> p' \<notin> C' \<longrightarrow> C \<union> C' \<noteq> UNIV" for C C'
      have "intertwined p p'"
      proof -
        { fix O O'
          assume "open O" and "open O'" and "p \<in> O" and "p' \<in> O'"
          have "O int O'" \<comment> \<open>Here we just instantiate the assumption above with the complements of our open sets\<close>
            using a0[of "-O" "-O'"]
            using \<open>open O'\<close> \<open>open O\<close> \<open>p \<in> O\<close> \<open>p' \<in> O'\<close> complement_open_is_closed intersects_def by auto }
        thus ?thesis 
          using def_3_6_1 by auto
      qed }
    ultimately show ?thesis
      by blast
  qed
  thus ?thesis
    by blast
qed
   
end

section "Finding examples with Nitpick"

text \<open>
  Here we restrict the union axiom to pairwise union to make it easier to find small models with Nitpick.
\<close>

nitpick_params [timeout = 120]

subsection "definitions"

locale semitopology_alt =
  fixes "open" :: "'a set \<Rightarrow> bool" \<comment> \<open>open seems to be reserved\<close>
  assumes "\<And> O O' . \<lbrakk>open O; open O'\<rbrakk> \<Longrightarrow> open (O \<union> O')" \<comment> \<open>using just pairwise union in an attempt to appease Nitpick\<close>
    and "open {}" and "open UNIV"
begin


definition intersects :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "int" 100)
  where "intersects a b \<equiv> a \<inter> b \<noteq> {}"

definition closure where
  "closure R \<equiv> {p . \<forall> O . open O \<and> p \<in> O \<longrightarrow> O int R}"

definition transitive 
  where "transitive S \<equiv> \<forall> O O' . open O \<and> open O' \<and> S int O \<and> S int O' \<longrightarrow> O int O'"

definition topen where
  "topen S \<equiv> open S \<and> transitive S"

definition strong_topen where
  "strong_topen S \<equiv> open S \<and> (\<forall> O O' . open O \<and> open O' \<and> S int O \<and> S int O' \<longrightarrow> O \<inter> O' \<inter> S \<noteq> {})"

definition intertwined where
  "intertwined p p' == transitive {p, p'}"

definition intertwined_set_of where
  "intertwined_set_of p \<equiv> {p' . intertwined p p'}"

definition closed where
  "closed R \<equiv> R = closure R"

definition interior where
  "interior R \<equiv> \<Union> {O . open O \<and> O \<subseteq> R}"

definition boundary where
  "boundary R \<equiv> R - interior R"

definition edge where
  "edge p \<equiv> boundary (intertwined_set_of p)"

definition K where
  \<comment> \<open>The community of a point\<close>
  "K p \<equiv> interior {p' . intertwined p p'}"

definition regular where
  "regular p \<equiv> p \<in> K p \<and> topen (K p)"

definition weakly_regular where
  "weakly_regular p  \<equiv>  p \<in> (K p)"

definition conflicted where
  "conflicted p  \<equiv> \<exists> p'. \<exists> p''. ((intertwined p' p)  \<and> (intertwined p p'')  \<and> \<not> (intertwined p' p''))"

definition unconflicted where
  "unconflicted p  \<equiv> \<forall> p'. \<forall> p''. intertwined p' p  \<and> intertwined p p''   \<longrightarrow>  intertwined p' p''"

definition dense_in where
  "dense_in D P  \<equiv>  (D \<subseteq> P) \<and> (\<forall> O. open O \<and> O \<noteq> {} \<and> O \<subseteq> P  \<longrightarrow> D int O)"

definition strongly_dense_in where
  "strongly_dense_in D P  \<equiv>  (D \<subseteq> P) \<and> (\<forall> O. open O \<and> P int O  \<longrightarrow> D int O)"

definition resilient where
  "resilient S \<equiv> \<forall> C . closed C \<longrightarrow> strong_topen (S - C)"

definition atom where
  "atom A \<equiv> A \<noteq> {} \<and> open A \<and> (\<forall> O . \<not> (O \<noteq> {} \<and> open O \<and> O \<subset> A))"

definition cover where
  "cover p O \<equiv> open O \<and> p \<in> O \<and> (\<forall> O' . \<not>(open O' \<and> p\<in>O' \<and> O' \<subset> O))"

definition kernel_atom where
  "kernel_atom p A \<equiv> atom A \<and> A \<subseteq> K p"

definition kernel where
  "kernel p \<equiv> {A . kernel_atom p A}"

subsection "Finding models..."

lemma "topen {}"
  \<comment> \<open>Just checking...\<close>
  by (metis inf_bot_left local.intersects_def local.transitive_def semitopology_alt_axioms semitopology_alt_def topen_def)

lemma
  fixes S1 S2 
  assumes "resilient S1" and "resilient S2"
    and "S1 \<inter> S2 \<noteq> {}"
  shows "resilient (S1 \<union> S2)"
  nitpick[verbose, card 'a=5, timeout=30000] \<comment> \<open>okay up to 8\<close>
  oops

lemma
  fixes S1 O
  assumes "resilient S1" and "open O" and "O \<inter> S1 \<noteq> {}"
  shows "S1 \<subseteq> closure O"
  nitpick[verbose, card 'a=5, timeout=3000] \<comment> \<open>okay up to 8\<close>
  oops

lemma \<comment> \<open>This is to find an example satisfying all the premises.\<close>
  fixes p I C Cl
  assumes "I = intertwined_set_of p"
    and "Cl = closure {p}"
    and "closed C" and "p \<in> interior C" and "\<forall> C' . closed C' \<and> p \<in> interior C' \<longrightarrow> \<not> C' \<subset> C"
    and "Cl \<subset> I" and "I \<subset> C"
  shows False
  nitpick[card 'a=4, verbose]
  oops

lemma closure_is_intertwined_set:
  fixes p O
  assumes "open O" and "p \<in> O" and "O \<subseteq> {p' . intertwined p p'}"
  shows "closure O = {p' . intertwined p p'}"
  oops


lemma \<comment> \<open>Space in which every point is unconflicted but not weakly regular'\<close>
  assumes "(\<forall> p. \<not> weakly_regular p \<and> unconflicted p)"
  shows False
  nitpick[card 'a=4]
  oops


lemma \<comment> \<open>Space in which every point is weakly regular but conflicted (nitpick fails because impossible)\<close>
  assumes "(\<forall> p. weakly_regular p \<and> conflicted p)"
  shows False
  nitpick[card 'a=1]
  oops

lemma \<comment> \<open>Space in which every point is weakly regular but not regular (nitpick fails because impossible)\<close>
  assumes "\<forall> p. weakly_regular p \<and> \<not> regular p"
  shows False
  nitpick[card 'a=1]
  oops

lemma \<comment> \<open>An unconflicted point on the boundary of a regular p\<close>
  fixes p q
  assumes "regular p" and "q \<in> edge p" and " \<not> conflicted q"
  shows False
  nitpick[card 'a=4]
  oops

lemma \<comment> \<open>A conflicted point on the boundary of a regular p\<close>
  fixes p q
  assumes "regular p" and "q \<in> edge p" and "conflicted q" and "weakly_regular q"
  shows False
  nitpick[card 'a=3]
  oops


lemma \<comment> \<open>A regular point on the boundary of a regular p (fails because impossible)\<close>
  fixes p q
  assumes "regular p" and "q \<in> edge p" and "regular q"
  shows False
  nitpick[card 'a=2]
  oops

lemma \<comment> \<open>A conflicted, not weakly regular point\<close>
  fixes p
  assumes "conflicted p" and "\<not> weakly_regular p"
  shows False 
  nitpick[card 'a=5]
  oops

lemma \<comment> \<open>A conflicted, not weakly regular point on a boundary\<close>
  fixes p q
  assumes "conflicted p" and "\<not> weakly_regular p" and "p \<in> edge q"
  shows False 
  nitpick[card 'a=5]
  oops

lemma \<comment> \<open>A point on the boundary of a closed set that is not intertwined with any element of its interior\<close>
  fixes p C 
  assumes "closed C" and "interior C \<noteq> {}" and "\<forall> q . \<not> (q\<in> interior C \<and> intertwined p q)" and "p \<in> boundary C"
  shows False 
  nitpick[card 'a=3]
  oops

lemma \<comment> \<open>A point that is unconflicted but on the intersection of the boundary of two closed neighbourhoods whose intersections do not intersect\<close>
  fixes p C C' 
  assumes "closed C" and "closed C'" and "interior C \<noteq> {}" and "interior C' \<noteq> {}" and "p \<in> boundary C" and "p \<in> boundary C'" and "\<not> (interior C) int (interior C')" and "\<not> conflicted p" 
  shows False 
  nitpick[card 'a=4]
  oops

lemma \<comment> \<open>A point that is regular but on the intersection of the boundary of two closed neighbourhoods whose intersections do not intersect, and p is not intertwined with any point in the interiors of either closed neighbourhoods\<close>
  fixes p C C' 
  assumes "closed C" and "closed C'" and "interior C \<noteq> {}" and "interior C' \<noteq> {}" and "p \<in> boundary C" and "p \<in> boundary C'" and "\<not> (interior C) int (interior C')" and "\<forall> q . \<not> (q\<in> interior C \<and> intertwined p q)" and "\<forall> q . \<not> (q\<in> interior C' \<and> intertwined p q)" and "regular p" 
  shows False 
  nitpick[card 'a=4]
  oops

lemma \<comment> \<open>Just because D is dense in P does not mean it is strongly dense)\<close>
  fixes D P
  assumes "open P" and "D \<noteq> {}" and "dense_in D P" 
  shows   " \<not> strongly_dense_in D P"
  nitpick[card 'a=2, verbose]
  oops

text 
  "Can p be in its community but the community of p not be a topen?
  As we see below, the answer is yes."

lemma
  fixes p Kp b
  assumes "Kp = K p" and "p \<in> Kp" and "\<not> topen Kp" and "b = (\<forall> p \<in> Kp . \<forall> p' \<in> Kp . intertwined p p')" and "\<not> b"
  shows False
  nitpick[card 'a=3]
  oops

lemma \<comment> \<open>A (wrong) conjecture:\<close>
  fixes p
  assumes "\<not> regular p" and "open O" and "p \<in> O" and "\<forall> p' \<in> O . intertwined p p'"
  shows False
  nitpick[card 'a=4, verbose]
  oops

lemma
  fixes p
  assumes "K p \<noteq> {}" and "\<not> transitive (K p)" and "\<not> p \<in> K p"
  shows False
  nitpick[card 'a=5, verbose]
  oops


lemma \<comment> \<open>If p is regular and A is an atom in p's community, it does not follow that p has a
    cover that includes A:\<close>
  fixes p A Kp
  assumes "regular p" and "atom A" and "A \<subseteq> Kp" and "Kp = K p"
  shows "\<exists> O . cover p O \<and> A \<subseteq> O"
  nitpick[card 'a=3]
  oops

lemma \<comment> \<open>no counterexample with 7 points\<close>
  fixes p Kp
  assumes "regular p"  and "Kp = K p"
  shows "\<exists> O . cover p O \<and> (\<forall> O' . atom O' \<and> transitive O' \<and> O' int O \<longrightarrow> O' \<subseteq> Kp)"
  oops

  text "Seems like the above should hold: Take a cover O inside the community of p.
  Then an O' as above must be in p-intertwined, and thus it's in the community (which this the
  interior of p-intertwined."

lemma \<comment> \<open>Example of a cover O of p that intersects an atom that goes outside the community, 
even though all transitive atoms that intersect O are within the community\<close>
  fixes p A Kp O
  assumes "regular p"  and "Kp = K p"
    and "cover p O \<and> (\<forall> O' . atom O' \<and> transitive O' \<and> O' int O \<longrightarrow> O' \<subseteq> Kp)"
    and "atom A" and "A int O" and "\<not> A \<subseteq> Kp"
  shows False
  nitpick[card 'a=4]
  oops

lemma 
  fixes p A O O'
  assumes "regular p"  and "cover p O" and "atom O'"
    and "transitive O'" and "O' int O"
  shows "O' \<subseteq> K p"
  nitpick[card 'a=3]
  oops

lemma \<comment> \<open>Second example requested by Jamie\<close>
  fixes C interior_C
  assumes "closed C" and "\<forall> C' . \<not>(interior C' \<noteq> {} \<and> closed C' \<and> C' \<subset> C)"
    and "interior C \<noteq> {}" and "\<not> topen interior_C" and "interior_C = interior C"
  shows False
  nitpick[card 'a=4]
  oops

end

end