-- Prove2me | Theorems.Thm_SchedComplexity_PrecChain_cmax_le_n_pstar
-- name    : SchedComplexity.PrecChain.cmax_le_n_pstar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:03:13.879765+00:00
-- url     : https://prove2.me/theorems/9d11d5e0-4e40-40cf-a211-13bde4ad7711
-- title:
--   Proof of Theorem 1(l) — every instance of n'|m|I,prec,1≤p_j1≤p_*|C_max has a schedule with C_max ≤ n'p_*
-- statement:
--   Let $p_*$ be a natural number and let $I$ be an instance of $n'|m|I,\mathit{prec},1\le p_{j1}\le p_*$: $n'$ jobs with processing times $1 \le p_j \le p_*$, $m \ge 1$ identical machines, and acyclic precedence constraints. Then $I$ has a feasible schedule with
--
--   $$C_{\max} \le n' p_*.$$
--
--   This bound is why, in the reduction of Theorem 1(l), only thresholds $0 \le y' \le n'p_*$ need to be considered: for larger $y'$ the answer is "yes".
--
--   **Formalization Note** "$C_{\max} \le n'p_*$" is stated as $C_j \le n'p_*$ for every job $j$. Acyclicity and $m \ge 1$ are part of the class (see the definition `SchedComplexity.PrecChain.Model`); without them the claim fails.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, proof of Theorem 1(l), first sentence

import Mathlib
import Definitions.Def_SchedComplexity_PrecChain_Model

namespace SchedComplexity.PrecChain

/-- Brucker, Lenstra & Rinnooy Kan (1975), proof of Theorem 1(l), p. 9: "Any instance of `P'`
has a solution with value `C_max ≤ n'p_*`." Every instance of
`n'|m|I,prec,1≤p_j1≤p_*|C_max` (at least one machine, processing times in `[1, p_*]`, acyclic
precedence) has a feasible schedule in which every job completes by `n' p_*`. -/
theorem cmax_le_n_pstar (pstar : ℕ) (I : Instance) (hI : I.InClass pstar) :
    CmaxYes I (I.n * pstar) := by sorry

end SchedComplexity.PrecChain
