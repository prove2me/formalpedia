-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaJSched_eq_3_1
-- name    : SingleMachineSched.AlphaJSched.eq_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:18:25.5813+00:00
-- url     : https://prove2.me/theorems/d4d51b9c-b131-4f96-946c-1f518130df23
-- title:
--   Eq. (3.1) — $M^{LP}_j=\int_0^1 t_j(\alpha)\,d\alpha$
-- statement:
--   Let $n$ jobs have integral processing times $p_j>0$, integral release dates $r_j\ge0$ and weights $w_j>0$, indexed in nonincreasing order of $w_j/p_j$. For every job $j$, the mean busy time of $j$ in the LP schedule is the average of its $\alpha$-points:
--   $$M^{LP}_j=\int_0^1 t_j(\alpha)\,d\alpha .$$
--
--   This identity turns a bound on the completion time of $j$ that is linear in $t_j(\alpha)$ into a bound in terms of $M^{LP}_j$ after integrating over a random $\alpha$.
--
--   **Formalization Note.** The integral is the Lebesgue integral over $(0,1]$ of $\alpha\mapsto t_j(\alpha)$, the $\alpha$-points taken in the LP schedule. The identity does not use the weights or their order; they are the paper's standing assumptions and are kept as hypotheses.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 176, Section 3, Eq. (3.1)

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaJSched_LPSchedule
import Definitions.Def_SingleMachineSched_AlphaJSched_AlphaPoints

namespace SingleMachineSched.AlphaJSched

/-- Equation (3.1): the mean busy time of job `j` in the LP schedule is the average of its
`α`-points over `α ∈ (0, 1]`. -/
theorem eq_3_1 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j) (j : Fin n) :
    mLP p r j = ∫ a in Set.Ioc (0 : ℝ) 1, alphaPoint p (lpSet p r) j a := by sorry

end SingleMachineSched.AlphaJSched
