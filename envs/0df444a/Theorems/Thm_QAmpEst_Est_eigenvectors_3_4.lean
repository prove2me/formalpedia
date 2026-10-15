-- Prove2me | Theorems.Thm_QAmpEst_Est_eigenvectors_3_4
-- name    : QAmpEst.Est.eigenvectors_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:19.157815+00:00
-- url     : https://prove2.me/theorems/09e5d3e5-54df-4851-917d-94021c3c4d93
-- title:
--   (3)–(5), p. 6 — for 0 < a < 1, Ψ± are orthonormal eigenvectors of Q with eigenvalues e^{±ı2θ_a}
-- statement:
--   In the setting of Lemma 1, suppose $0 < a < 1$ and let $\theta_a = \arcsin\sqrt a$. Then $\sin^2\theta_a = a$ and $0 \le \theta_a \le \pi/2$, and the two vectors
--   $$|\Psi_\pm\rangle = \frac{1}{\sqrt 2}\Big(\frac{1}{\sqrt a}|\Psi_1\rangle \pm \frac{\imath}{\sqrt{1-a}}|\Psi_0\rangle\Big)$$
--   are unit vectors, orthogonal to each other, and eigenvectors of $\mathbf Q$:
--   $$\mathbf Q|\Psi_\pm\rangle = e^{\pm\imath 2\theta_a}|\Psi_\pm\rangle .$$
--
--   This is the spectral picture behind amplitude estimation: estimating $a$ amounts to estimating the eigenphase $2\theta_a$ of $\mathbf Q$.
-- source:
--   arXiv:quant-ph/0005055v1, (3), (4) and (5), p. 6

import Mathlib
import Definitions.Def_QAmpEst_Est_Setting

open scoped Real Kronecker

namespace QAmpEst.Est

/-- Equations (3)–(5), arXiv:quant-ph/0005055v1, p. 6: for `0 < a < 1`, the vectors
`|Ψ±⟩ = (1/√2)((1/√a)|Ψ₁⟩ ± (ı/√(1 − a))|Ψ₀⟩)` form an orthonormal pair of eigenvectors of `Q`
with eigenvalues `λ± = e^{±ı2θ_a}`, where `θ_a = arcsin √a` satisfies `sin²(θ_a) = a` and
`0 ≤ θ_a ≤ π/2`. -/
theorem eigenvectors_3_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι)
    (ha0 : 0 < succProb A χ z0) (ha1 : succProb A χ z0 < 1) :
    let a := succProb A χ z0
    let Ψp := psiPlus A χ z0
    let Ψm := psiMinus A χ z0
    (Real.sin (theta a) ^ 2 = a ∧ 0 ≤ theta a ∧ theta a ≤ π / 2) ∧
      (∑ x, Complex.normSq (Ψp x) = 1) ∧ (∑ x, Complex.normSq (Ψm x) = 1) ∧
      (∑ x, star (Ψp x) * Ψm x = 0) ∧
      (Qop A χ z0).mulVec Ψp = Complex.exp (((2 * theta a : ℝ) : ℂ) * Complex.I) • Ψp ∧
      (Qop A χ z0).mulVec Ψm = Complex.exp (((-(2 * theta a)) : ℝ) * Complex.I) • Ψm := by sorry

end QAmpEst.Est
