-- Prove2me | Theorems.Thm_QubitPhaseEst_eq_8
-- name    : QubitPhaseEst.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:26.930887+00:00
-- url     : https://prove2.me/theorems/d6ed3fcb-bdf0-41df-bd26-abfe09ed33d2
-- title:
--   Eq. (8): qubit infidelity $1-F(\phi)=\frac{n_x^2+n_y^2}{2}(1-\cos\phi)$ (corrected: $r^2\to n_x^2+n_y^2$)
-- statement:
--   Let $\vec n=(n_x,n_y,n_z)$ with $n_x^2+n_y^2+n_z^2<1$, let $\rho=\tfrac12(I+\vec n\cdot\vec\sigma)$ and $u_\phi=e^{-i\phi\sigma_z/2}$. For every $\phi\in\mathbb R$ the Uhlmann infidelity between $\rho$ and $u_\phi\rho u_\phi^\dagger$ is
--
--   $$
--   1-F(\phi)=\frac{n_x^2+n_y^2}{2}\,(1-\cos\phi).
--   $$
--
--   So the fidelity cost depends on $\phi$ only through $\cos\phi$, which is what reduces the fidelity criterion to the averaged cosine.
--
--   Differences from the source:
--   - correction: 1 − F(φ) = (r²/2)(1 − cos φ) → 1 − F(φ) = ((n_x² + n_y²)/2)(1 − cos φ); reason: for n = (0, 0, 0.6) and φ = 1.1, u_φ commutes with ρ and 1 − F = 0, while the printed (8) gives 0.0984; the two agree when n_z = 0, as in the paper's equatorial case
--   - encoding: |n| < 1 → n_x² + n_y² + n_z² < 1; reason: the default norm on Fin 3 → ℝ is the sup norm, so the Euclidean condition is written out
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eq. (8), p. 2

import Mathlib
import Definitions.Def_QubitPhaseEst_blochState
import Definitions.Def_QubitPhaseEst_infidCost

open scoped Matrix ComplexOrder

namespace QubitPhaseEst

/-- **Eq. (8), corrected.** arXiv:quant-ph/0411133v3, Sec. II, Eq. (8), p. 2: for a qubit state with
Bloch vector `n`, `1 − F(φ) = ((n_x² + n_y²)/2)(1 − cos φ)`.

**Formalization Note.** The printed (8) has `r²` in place of `n_x² + n_y²`; that is false for
`n_z ≠ 0` (for `n = (0, 0, 0.6)` the left side is `0`, because `u_φ` commutes with `ρ`). The two agree
when `n_z = 0`. The paper's `|n| < 1` is written with the Euclidean square, since the default norm on
`Fin 3 → ℝ` is the sup norm. -/
theorem eq_8 (n : Fin 3 → ℝ) (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 < 1) (φ : ℝ) :
    infidCost (blochState n) φ = (n 0 ^ 2 + n 1 ^ 2) / 2 * (1 - Real.cos φ) := by sorry

end QubitPhaseEst
