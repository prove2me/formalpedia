-- Prove2me | Theorems.Thm_QubitPhaseEst_costs_through_cosine
-- name    : QubitPhaseEst.costs_through_cosine
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:27.710156+00:00
-- url     : https://prove2.me/theorems/e01a693f-1c16-47e0-913b-2d31487de92d
-- title:
--   Costs through the cosine: $\langle v\rangle=2(1-\langle c\rangle)$, $\langle 1-F\rangle=\frac{n_x^2+n_y^2}{2}(1-\langle c\rangle)$ (corrected: $r^2\to n_x^2+n_y^2$ from Eq. (8))
-- statement:
--   Let $\vec n$ satisfy $n_x^2+n_y^2+n_z^2<1$, let $\rho=\rho_{\vec n}$ and $R=\rho^{\otimes N}$, and let $\xi$ be the seed of a covariant POVM. Write $\langle c\rangle$ for the averaged cosine of $\xi$. Then the averaged periodicized variance and the averaged Uhlmann infidelity are
--
--   $$
--   \langle v\rangle=2\bigl(1-\langle c\rangle\bigr),\qquad \langle 1-F\rangle=\frac{n_x^2+n_y^2}{2}\bigl(1-\langle c\rangle\bigr).
--   $$
--
--   Hence a seed that maximizes $\langle c\rangle$ minimizes both averaged costs, which is why the paper maximizes the averaged cosine (9).
--
--   Differences from the source:
--   - reading: both cost functions depend on φ only through its cosine, whence one maximizes ⟨c⟩ → the explicit affine relations between the averaged costs and ⟨c⟩; reason: this is what the sentence asserts once (6) and (8) are averaged against a normalized POVM
--   - correction: coefficient r²/2 of Eq. (8) → coefficient (n_x² + n_y²)/2; reason: Eq. (8) is false off the equator (counterexample in QubitPhaseEst.eq_8)
--   - generalization: n with no y component → every Bloch vector with n_x² + n_y² + n_z² < 1; reason: specializes to the paper at n_y = 0
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, p. 2, sentence before Eq. (9), with Eqs. (6) and (8)

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_QubitPhaseEst_blochState
import Definitions.Def_QubitPhaseEst_IsSeed
import Definitions.Def_QubitPhaseEst_avgCost
import Definitions.Def_QubitPhaseEst_infidCost

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **Both costs depend on `φ` only through its cosine.** arXiv:quant-ph/0411133v3, Sec. II, p. 2,
before Eq. (9): for an admissible seed, the averaged periodicized variance is `2(1 − ⟨c⟩)` and the
averaged infidelity is `((n_x² + n_y²)/2)(1 − ⟨c⟩)`, where `⟨c⟩ = avgCost Real.cos R ξ` is the
averaged cosine of Eq. (9). So maximizing `⟨c⟩` minimizes both.

**Formalization Note.** The infidelity coefficient is that of the corrected Eq. (8) (see
`QubitPhaseEst.eq_8`). -/
theorem costs_through_cosine {N : ℕ} (n : Fin 3 → ℝ) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 < 1)
    (ξ : Matrix (Qb N) (Qb N) ℂ) (hξ : IsSeed ξ) :
    avgCost vCost (ShadowTomography.UpperBound.tensorPow (blochState n) N) ξ =
        2 * (1 - avgCost Real.cos (ShadowTomography.UpperBound.tensorPow (blochState n) N) ξ) ∧
      avgCost (infidCost (blochState n)) (ShadowTomography.UpperBound.tensorPow (blochState n) N) ξ =
        (n 0 ^ 2 + n 1 ^ 2) / 2 * (1 - avgCost Real.cos (ShadowTomography.UpperBound.tensorPow (blochState n) N) ξ) := by sorry

end QubitPhaseEst
