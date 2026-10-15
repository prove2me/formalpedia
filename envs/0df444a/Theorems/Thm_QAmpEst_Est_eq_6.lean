-- Prove2me | Theorems.Thm_QAmpEst_Est_eq_6
-- name    : QAmpEst.Est.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:09.529045+00:00
-- url     : https://prove2.me/theorems/62acc0c7-8496-4982-a69d-bb4f65f67864
-- title:
--   (6), p. 6 — A|0⟩ = (−ı/√2)(e^{ıθ_a}Ψ₊ − e^{−ıθ_a}Ψ₋) for 0 < a < 1
-- statement:
--   In the setting of Lemma 1, suppose $0 < a < 1$, and let $|\Psi_\pm\rangle$ and $\theta_a$ be as in (3)–(5). Then the initial state, expressed in the eigenvector basis of $\mathbf Q$, is
--   $$\mathcal A|0\rangle = |\Psi\rangle = \frac{-\imath}{\sqrt 2}\Big(e^{\imath\theta_a}|\Psi_+\rangle - e^{-\imath\theta_a}|\Psi_-\rangle\Big).$$
--
--   Together with (4) this gives the state after any number of applications of $\mathbf Q$, and it is the starting point of the analysis of $\mathbf{Est\_Amp}$.
-- source:
--   arXiv:quant-ph/0005055v1, (6), p. 6

import Mathlib
import Definitions.Def_QAmpEst_Est_Setting

open scoped Real Kronecker

namespace QAmpEst.Est

/-- Equation (6), arXiv:quant-ph/0005055v1, p. 6: for `0 < a < 1`,
`A|0⟩ = |Ψ⟩ = (−ı/√2)(e^{ıθ_a}|Ψ₊⟩ − e^{−ıθ_a}|Ψ₋⟩)`. -/
theorem eq_6 {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι)
    (ha0 : 0 < succProb A χ z0) (ha1 : succProb A χ z0 < 1) :
    let θ := theta (succProb A χ z0)
    initState A z0 =
      (-Complex.I / (Real.sqrt 2 : ℂ)) •
        (Complex.exp ((θ : ℂ) * Complex.I) • psiPlus A χ z0 -
          Complex.exp (-(θ : ℂ) * Complex.I) • psiMinus A χ z0) := by sorry

end QAmpEst.Est
