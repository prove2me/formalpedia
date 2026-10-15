-- Prove2me | Theorems.Thm_QAmpEst_Est_state_after_ctrlPow
-- name    : QAmpEst.Est.state_after_ctrlPow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:16.808633+00:00
-- url     : https://prove2.me/theorems/282c801e-c224-4183-8631-de4ee3035f28
-- title:
--   Proof of Theorem 12, p. 20 — after Λ_M(Q) the state is −ı((e^{ıθ_a}/√2)|S_M(θ_a/π)⟩|Ψ₊⟩ − (e^{−ıθ_a}/√2)|S_M(1 − θ_a/π)⟩|Ψ₋⟩)
-- statement:
--   In the setting of Lemma 1, let $M \ge 1$ and suppose $0 < a < 1$. Prepare $|0\rangle\mathcal A|0\rangle$, apply $F_M$ to the first register and then $\Lambda_M(\mathbf Q)$ (steps 1–3 of $\mathbf{Est\_Amp}$). The resulting state is
--   $$-\imath\Big(\frac{e^{\imath\theta_a}}{\sqrt 2}\,|S_M(\theta_a/\pi)\rangle|\Psi_+\rangle - \frac{e^{-\imath\theta_a}}{\sqrt 2}\,|S_M(1-\theta_a/\pi)\rangle|\Psi_-\rangle\Big).$$
--
--   The first register thus carries the two eigenphases of $\mathbf Q$ as phase states, entangled with the corresponding eigenvectors.
--
--   **Formalization Note** The paper drops the global phase $-\imath$ after step 2 ("ignoring global phase", p. 19); here it is kept, since an equation between vectors is false without it.
-- source:
--   arXiv:quant-ph/0005055v1, proof of Theorem 12, p. 20 (first display); p. 19

import Mathlib
import Definitions.Def_QAmpEst_Est_Setting

open scoped Real Kronecker

namespace QAmpEst.Est

/-- Proof of Theorem 12, arXiv:quant-ph/0005055v1, p. 20, first display: for `0 < a < 1`,
after steps 1–3 of `Est_Amp(A, χ, M)` (prepare `|0⟩A|0⟩`, apply `F_M ⊗ I`, apply `Λ_M(Q)`) the
state is
`−ı ((e^{ıθ_a}/√2)|S_M(θ_a/π)⟩|Ψ₊⟩ − (e^{−ıθ_a}/√2)|S_M(1 − θ_a/π)⟩|Ψ₋⟩)`.
The global phase `−ı`, which the page drops ("ignoring global phase", p. 19), is kept. -/
theorem state_after_ctrlPow {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) (M : ℕ) (hM : 0 < M)
    (ha0 : 0 < succProb A χ z0) (ha1 : succProb A χ z0 < 1) :
    let θ := theta (succProb A χ z0)
    (ctrlPow M (Qop A χ z0) * (ShorAlgorithms.Shared.fourierMatrix M ⊗ₖ (1 : Matrix ι ι ℂ))).mulVec (estAmpInput M A z0) =
      fun p => -Complex.I *
        ((Complex.exp ((θ : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)) * stateS M (θ / π) p.1 *
            psiPlus A χ z0 p.2 -
          (Complex.exp (-(θ : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)) * stateS M (1 - θ / π) p.1 *
            psiMinus A χ z0 p.2) := by sorry

end QAmpEst.Est
