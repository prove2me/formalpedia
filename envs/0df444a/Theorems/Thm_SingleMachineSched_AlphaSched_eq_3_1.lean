-- Prove2me | Theorems.Thm_SingleMachineSched_AlphaSched_eq_3_1
-- name    : SingleMachineSched.AlphaSched.eq_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:11:54.99848+00:00
-- url     : https://prove2.me/theorems/48c54cd2-a820-4d17-9142-e4f97cc9046b
-- title:
--   Eq. (3.1) — the mean busy time is the average of the $\alpha$-points
-- statement:
--   Let $n$ jobs have integral processing times $p_j > 0$, integral release dates $r_j \ge 0$ and weights $w_j > 0$, indexed by nonincreasing $w_j/p_j$. For every job $j$, the mean busy time of $j$ in the LP schedule is the average over $\alpha \in (0,1]$ of its $\alpha$-points in the LP schedule:
--
--   $$M^{LP}_j = \int_0^1 t_j(\alpha)\, d\alpha .$$
--
--   This identity turns bounds on completion times stated in terms of $\alpha$-points into bounds in terms of $M^{LP}_j$, and hence of the LP value.
--
--   **Formalization Note** The integral is the Lebesgue integral over $(0, 1]$. Since $M^{LP}_j \ge r_j + p_j/2 > 0$, the identity cannot hold through the convention that a non-integrable function has integral $0$. The weights and the sortedness are the paper's standing assumptions; the identity itself concerns only the LP schedule.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 176, Eq. (3.1)

import Mathlib
import Definitions.Def_SingleMachineSched_AlphaSched_AlphaPoints

namespace SingleMachineSched.AlphaSched

open MeasureTheory

/-- Eq. (3.1) (Goemans et al. 2002, p. 176): the mean busy time of job `j` in the LP schedule is
the average of its `α`-points, `M^LP_j = ∫_0^1 t_j(α) dα`. -/
theorem eq_3_1 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 < w j)
    (hsort : ∀ j k : Fin n, j ≤ k → w k / p k ≤ w j / p j) (j : Fin n) :
    mLP p r j = ∫ a in Set.Ioc (0 : ℝ) 1, alphaPoint p (lpSet p r) j a := by sorry

end SingleMachineSched.AlphaSched
