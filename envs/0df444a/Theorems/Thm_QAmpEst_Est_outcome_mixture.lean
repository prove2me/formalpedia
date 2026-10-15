-- Prove2me | Theorems.Thm_QAmpEst_Est_outcome_mixture
-- name    : QAmpEst.Est.outcome_mixture
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:16.883927+00:00
-- url     : https://prove2.me/theorems/0f836339-60e6-4843-8bc4-8500deba8290
-- title:
--   Proof of Theorem 12, p. 20 — the outcome law is the even mixture of the laws for S_M(θ_a/π) and S_M(1 − θ_a/π); y ↔ M − y
-- statement:
--   In the setting of Lemma 1, let $M \ge 1$, suppose $0 < a < 1$, and write $P_\omega(y)$ for the probability of measuring $y$ in $F_M^{-1}|S_M(\omega)\rangle$.
--
--   1. The outcome $y$ of $\mathbf{Est\_Amp}(\mathcal A,\chi,M)$ has the law of an equally weighted mixture:
--   $$\mathrm{Prob}(y) = \tfrac12 P_{\theta_a/\pi}(y) + \tfrac12 P_{1-\theta_a/\pi}(y) \qquad (0 \le y < M).$$
--   2. For every real $\omega$ and every $y$, $P_{1-\omega}(y) = P_\omega(M-y)$, where $M - y$ is read modulo $M$ (so it is $0$ when $y = 0$).
--
--   These two facts reduce Theorem 12 to Theorem 11 applied at $\omega = \theta_a/\pi$.
-- source:
--   arXiv:quant-ph/0005055v1, proof of Theorem 12, p. 20 (second paragraph)

import Mathlib
import Definitions.Def_QAmpEst_Est_Setting

open scoped Real Kronecker

namespace QAmpEst.Est

/-- Proof of Theorem 12, arXiv:quant-ph/0005055v1, p. 20, second paragraph: for `0 < a < 1`,
the first register is an equally weighted mixture of `F_M⁻¹|S_M(θ_a/π)⟩` and
`F_M⁻¹|S_M(1 − θ_a/π)⟩`, so `Prob(y) = ½ P_{θ_a/π}(y) + ½ P_{1−θ_a/π}(y)`; and the probability of
measuring `|y⟩` given `F_M⁻¹|S_M(1 − ω)⟩` equals that of measuring `|M − y⟩` (read mod `M`)
given `F_M⁻¹|S_M(ω)⟩`. -/
theorem outcome_mixture {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A ∈ Matrix.unitaryGroup ι ℂ) (χ : ι → Bool) (z0 : ι) (M : ℕ) (hM : 0 < M)
    (ha0 : 0 < succProb A χ z0) (ha1 : succProb A χ z0 < 1) :
    (∀ y : Fin M, outcomeProb M A χ z0 y =
        phaseProb M (theta (succProb A χ z0) / π) y / 2 +
          phaseProb M (1 - theta (succProb A χ z0) / π) y / 2) ∧
      (∀ ω : ℝ, ∀ y : Fin M, phaseProb M (1 - ω) y = phaseProb M ω (-y)) := by sorry

end QAmpEst.Est
