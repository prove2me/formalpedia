-- Prove2me | Theorems.Thm_SchedComplexity_Tardiness_theorem_4d_knapsack_reducible
-- name    : SchedComplexity.Tardiness.theorem_4d_knapsack_reducible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:07:13.696107+00:00
-- url     : https://prove2.me/theorems/f48ade2d-1edc-4901-9ac0-f681f2a83a2a
-- title:
--   Theorem 4(d) — KNAPSACK is polynomially reducible to $n|1||\sum w_jT_j$
-- statement:
--   Theorem 4 of the paper (p. 16) reads: "KNAPSACK is reducible to the following problems: (a) $n|1|r_n\ge0,w_j=1|\sum w_jC_j$; (b) $n|1|L_{\max}\le0|\sum w_jC_j$; (c) $n|1|r_n\ge0|L_{\max}$; (d) $n|1||\sum w_jT_j$; (e) $n|1||\sum w_jU_j$; (f) $n|1|r_n\ge0,w_j=1|\sum w_jU_j$; (g) $n|2|F,r_n\ge0|C_{\max}$; (h) $n|2|F,tree|C_{\max}$; (i) $n|2|G,m_j\le3|C_{\max}$; (j) $n|3|G,m_j\le2|C_{\max}$." Only part (d) is formalized here:
--
--   $$\text{KNAPSACK}\;\propto\;n|1||\textstyle\sum w_jT_j .$$
--
--   Reducibility (Section 2, p. 4) is polynomial-time many-one reducibility of the recognition problems: there is a function $f$ on words, computable by a Turing machine in polynomial time, such that a word is the code of a KNAPSACK yes-instance (positive integers $a_1,\dots,a_t,b$ with $\sum_{j\in S}a_j=b$ for some $S$) if and only if $f$ of it is the code of a yes-instance of $n|1||\sum w_jT_j$: a single-machine instance with processing times, weights and due dates, together with a threshold $y$, that has a feasible schedule with $\sum_j w_jT_j\le y$.
--
--   The instances of $n|1||\sum w_jT_j$ are encoded as in the paper's Remark (p. 23): each class of jobs with identical data is written once, with its cardinality. "In the last two reductions the size of the scheduling problem depends on $A$ and $a_*$. It can be questioned if these reductions are truly polynomial-bounded: in some encodings the length of the scheduling input string is polynomial in $A$ and $a_*$ and thus exponential in the length of the KNAPSACK input string, the latter one being proportional to $\log_2a_*$. We may settle this question, however, by characterizing a subset of jobs with identical data $(p_{jr},w_j,r_j,d_j)$ by its cardinality and a single copy of the data."
--
--   Since KNAPSACK is NP-complete (Karp), the theorem shows that minimizing total weighted tardiness on a single machine is NP-hard.
--
--   **Formalization Note** Reducibility is `CookPvsNP.PolyReducible` from the published `CookPvsNP_defs` (Turing machines with an explicit polynomial time bound), over the alphabet `BSym` of the published `ProjSchedTW.Complexity.Encoding`. The source language `SchedComplexity.OneMachine.knapsackLang` (the shared KNAPSACK language) codes $b,a_1,\dots,a_t$ in binary and requires all of them positive; the target language `wtLangMult` uses the multiplicity encoding (`MultLang`). Under the one-copy-per-job encoding the paper does not claim polynomiality. The paper's "we may assume that $0<b<A$" is not an assumption here: the reduction must handle all KNAPSACK instances.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 16, Theorem 4(d); proof pp. 20–21; Remark p. 23

import Mathlib
import Definitions.Def_SchedComplexity_Tardiness_Knapsack
import Definitions.Def_SchedComplexity_Tardiness_MultLang

namespace SchedComplexity.Tardiness

open CookPvsNP in
/-- Theorem 4(d), p. 16 (proof pp. 20–21, Remark p. 23): KNAPSACK is polynomial-time many-one
reducible to `n|1||Σw_jT_j`, the latter encoded with job multiplicities as in the Remark. -/
theorem theorem_4d_knapsack_reducible : PolyReducible SchedComplexity.OneMachine.knapsackLang wtLangMult := by sorry

end SchedComplexity.Tardiness
