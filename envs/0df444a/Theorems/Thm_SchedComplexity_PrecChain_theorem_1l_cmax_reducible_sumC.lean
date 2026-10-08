-- Prove2me | Theorems.Thm_SchedComplexity_PrecChain_theorem_1l_cmax_reducible_sumC
-- name    : SchedComplexity.PrecChain.theorem_1l_cmax_reducible_sumC
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:18:02.117927+00:00
-- url     : https://prove2.me/theorems/36b67b60-fa37-4652-bb65-d6f006b749f7
-- title:
--   Theorem 1(l) — n'|m|I,prec,1≤p_j1≤p_*|C_max ∝ n|m|I,prec,1≤p_j1≤p_*,w_j=1|Σw_jC_j
-- statement:
--   Let $p_* \ge 1$ be a constant. Consider the recognition problem $P'$: given $n'$ single-operation jobs with processing times $1 \le p_j \le p_*$, $m \ge 1$ identical machines, acyclic precedence constraints and a threshold $y'$, is there a feasible schedule with $C_{\max} \le y'$? And the recognition problem $P$: given an instance of the same class and a threshold $y$, is there a feasible schedule with $\sum_j C_j \le y$ (all weights $w_j = 1$)? Then
--
--   $$n'|m|I,\mathit{prec},1\le p_{j1}\le p_*|C_{\max} \;\propto\; n|m|I,\mathit{prec},1\le p_{j1}\le p_*,w_j=1|\textstyle\sum w_jC_j,$$
--
--   that is, there is a function computable in polynomial time that maps every code of an instance of $P'$ to a code of an instance of $P$ such that the first is a yes-instance if and only if the second is.
--
--   By Theorem 1(b), any NP-completeness result for the makespan problem on the left thus transfers to the total completion time problem on the right; Table III of the paper applies this to results of Ullman.
--
--   **Formalization Note** Reducibility is Cook's polynomial-time many-one reducibility `CookPvsNP.PolyReducible` between the binary languages of `SchedComplexity.PrecChain.Languages`. The constant $p_*$ is fixed outside both languages; the size of the constructed instance is polynomial only because $p_*$ is a constant.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, Theorem 1(l)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SchedComplexity_PrecChain_Languages

namespace SchedComplexity.PrecChain

/-- Brucker, Lenstra & Rinnooy Kan (1975), Theorem 1(l), p. 9:
`n'|m|I,prec,1≤p_j1≤p_*|C_max ∝ n|m|I,prec,1≤p_j1≤p_*,w_j=1|Σw_jC_j`. For every constant
`p_* ≥ 1`, the recognition version of makespan minimization on identical machines with
precedence constraints and processing times in `[1, p_*]` is polynomial-time many-one reducible
(Cook's Definition 3) to the recognition version of total completion time minimization in the
same class. -/
theorem theorem_1l_cmax_reducible_sumC (pstar : ℕ) (hpstar : 1 ≤ pstar) :
    CookPvsNP.PolyReducible (cmaxLang pstar) (sumCLang pstar) := by sorry

end SchedComplexity.PrecChain
