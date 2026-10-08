-- Prove2me | Theorems.Thm_SchedComplexity_NoWait_theorem_5_hamilton_path_reducible
-- name    : SchedComplexity.NoWait.theorem_5_hamilton_path_reducible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:02:40.680862+00:00
-- url     : https://prove2.me/theorems/901b17c7-fd1f-4472-a961-368e4c814f55
-- title:
--   Theorem 5 — DIRECTED HAMILTON PATH ∝ n|m|F,no wait|C_max and ∝ n|m|F,no wait,w_j=1|Σw_jC_j
-- statement:
--   **Theorem 5** (Brucker, Lenstra & Rinnooy Kan). DIRECTED HAMILTON PATH is reducible to the following problems:
--
--   1. $n|m|F,\textit{no wait}|C_{\max}$;
--   2. $n|m|F,\textit{no wait},w_j=1|\sum w_jC_j$.
--
--   Here *reducible* ($P'\propto P$, Section 2) is polynomial-time many-one reducibility between the recognition languages: there is a function computable in polynomial time by a Turing machine that maps the code of every directed graph to the code of a pair (instance, threshold $y$) such that the graph has a Hamilton path iff the instance has a feasible no-wait schedule with value $\le y$; and inputs that are not codes of yes-instances go to codes of no-instances. The languages are the binary codes of directed graphs with a Hamilton path, and of pairs (no-wait flow shop instance, $y$) admitting a feasible schedule with $C_{\max}\le y$, respectively $\sum_j C_j\le y$.
--
--   Together with the NP-completeness of DIRECTED HAMILTON PATH (Theorem 2(d)) this shows that both no-wait flow shop problems, with the number of machines part of the input, are NP-complete.
--
--   **Formalization Note** Polynomial time is `CookPvsNP.PolyTimeComputable` (published `CookPvsNP_defs`). The paper's construction (pp. 24–25) needs an admissible ordering $\iota$, which exists for every $n\ne2$ but not for $n=2$; a reduction realizing the theorem has to decide graphs on at most two vertices directly (a Hamilton path there is checkable at once) and map them to a fixed yes- or no-instance. NP-membership is not part of the statement.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 24, Theorem 5 (proof pp. 24–25)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
import Definitions.Def_SchedComplexity_NoWait_NoWaitFlowShop

namespace SchedComplexity.NoWait

/-- Theorem 5 (p. 24): DIRECTED HAMILTON PATH is polynomial-time many-one reducible to
(a) `n|m|F,no wait|C_max` and to (b) `n|m|F,no wait,w_j=1|Σw_jC_j`. -/
theorem theorem_5_hamilton_path_reducible :
    CookPvsNP.PolyReducible dhpLang cmaxLang ∧
      CookPvsNP.PolyReducible dhpLang sumCLang := by sorry

end SchedComplexity.NoWait
