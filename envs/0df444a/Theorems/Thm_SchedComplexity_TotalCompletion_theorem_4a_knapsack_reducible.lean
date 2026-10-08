-- Prove2me | Theorems.Thm_SchedComplexity_TotalCompletion_theorem_4a_knapsack_reducible
-- name    : SchedComplexity.TotalCompletion.theorem_4a_knapsack_reducible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:09:46.582995+00:00
-- url     : https://prove2.me/theorems/67dca3cb-8082-4959-986a-e991d576c292
-- title:
--   Theorem 4(a): KNAPSACK is reducible to $n|1|r_n\ge0,w_j=1|\sum w_jC_j$
-- statement:
--   Brucker, Lenstra and Rinnooy Kan state (Theorem 4, p. 16):
--
--   > THEOREM 4. KNAPSACK is reducible to the following problems: (a) $n|1|r_n\ge0,w_j=1|\sum w_jC_j$; (b) $n|1|L_{\max}\le0|\sum w_jC_j$; (c) $n|1|r_n\ge0|L_{\max}$; (d) $n|1||\sum w_jT_j$; (e) $n|1||\sum w_jU_j$; (f) $n|1|r_n\ge0,w_j=1|\sum w_jU_j$; (g) $n|2|F,r_n\ge0|C_{\max}$; (h) $n|2|F,tree|C_{\max}$; (i) $n|2|G,m_j\le3|C_{\max}$; (j) $n|3|G,m_j\le2|C_{\max}$.
--
--   This item formalizes part (a). Here "reducible" is the paper's notion (Section 2): every instance of KNAPSACK can be transformed in polynomial time into an instance of the scheduling problem with the same answer. Precisely, there is a function $f$ on strings, computable in polynomial time, such that for every string $x$,
--
--   $$x\in\mathrm{KNAPSACK} \iff f(x)\in L\bigl(n|1|r_n\ge0,w_j=1|\textstyle\sum w_jC_j\bigr),$$
--
--   where KNAPSACK is the language of binary codes of solvable instances with positive entries, and the target language consists of the codes of pairs (instance, $y$) such that the instance has unit weights, release date $0$ for every job except the last, and a feasible single-machine schedule with $\sum_jC_j\le y$.
--
--   The target instances are written in the multiplicity encoding of the paper's Remark (p. 23): "In the last two reductions the size of the scheduling problem depends on $A$ and $a_*$. It can be questioned if these reductions are truly polynomial-bounded: in some encodings the length of the scheduling input string is polynomial in $A$ and $a_*$ and thus exponential in the length of the KNAPSACK input string, the latter one being proportional to $\log_2 a_*$. We may settle this question, however, by characterizing a subset of jobs with identical data $(p_{jr},w_j,r_j,d_j)$ by its cardinality and a single copy of the data." The last two reductions are (d) and (a).
--
--   With the NP-completeness of KNAPSACK (Theorem 2(b)) the result shows that the single-machine total completion time problem becomes NP-complete as soon as one job has a nonzero release date.
--
--   **Formalization Note** Reducibility is `CookPvsNP.PolyReducible` from the published definition `CookPvsNP_defs` (polynomial-time many-one reducibility in Cook's machine model); polynomiality is part of the statement. Numbers are coded in binary over the alphabet of `ProjSchedTW.Complexity.Encoding`. The target language uses the multiplicity encoding: a list of job types (count, processing time, weight, release date) and the threshold $y$, with class membership checked on the expanded job list. Under a one-entry-per-job encoding the construction is not polynomial and the paper does not claim the statement. Starting times are natural numbers (Section 3).
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 16, Theorem 4(a); proof pp. 22–23; Remark p. 23; Section 2, p. 4 (reducibility)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SchedComplexity_TotalCompletion_Knapsack
import Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine

namespace SchedComplexity.TotalCompletion

/-- Theorem 4(a) (p. 16; proof pp. 22–23; Remark p. 23): KNAPSACK is reducible to
`n|1|r_n≥0,w_j=1|Σw_jC_j`, as a polynomial-time many-one reduction (`CookPvsNP.PolyReducible`)
from the binary-coded KNAPSACK language to the language of the scheduling problem in the
multiplicity encoding of the Remark on p. 23. -/
theorem theorem_4a_knapsack_reducible :
    CookPvsNP.PolyReducible knapsackLang sumCLangMult := by sorry

end SchedComplexity.TotalCompletion
