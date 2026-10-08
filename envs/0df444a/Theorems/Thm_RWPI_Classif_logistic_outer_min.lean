-- Prove2me | Theorems.Thm_RWPI_Classif_logistic_outer_min
-- name    : RWPI.Classif.logistic_outer_min
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:53:07.078205+00:00
-- url     : https://prove2.me/theorems/59d3be1f-c5e5-41ee-8580-123d49ff8b4c
-- title:
--   Proof of Theorem 2, p. 30 — the outer minimisation over λ for logistic regression
-- statement:
--   Let $p, q \in [1,\infty]$ satisfy $1/p + 1/q = 1$. Let $(X_1,Y_1),\dots,(X_n,Y_n) \in \mathbb R^d \times \{-1,+1\}$ with $n \ge 1$, let $\beta \in \mathbb R^d$ and $\delta \ge 0$. Then
--
--   $$\inf_{\lambda \ge 0}\Big\{ \delta\lambda + \frac1n\sum_{i=1}^n \sup_{x\in\mathbb R^d}\Big\{ \log\big(1+\exp(-Y_i\beta^T x)\big) - \lambda\|x - X_i\|_q \Big\}\Big\} = \frac1n\sum_{i=1}^n \log\big(1+\exp(-Y_i\beta^T X_i)\big) + \delta\,\|\beta\|_p .$$
--
--   Combined with Proposition 1, the left-hand side is the worst-case expected logistic loss over the ball $\{P : D_{N_q}(P,P_n)\le\delta\}$; the identity is therefore the per-$\beta$ form of the logistic half of Theorem 2.
--
--   **Formalization Note** The paper's chain passes through indicators printed as $\mathbf 1_{\{\lambda > \|\beta\|\}}$ and $\infty\,\mathbf 1_{\{\lambda \le \|\beta\|\}}$; by the previous step the inner supremum is finite at $\lambda = \|\beta\|$, so the correct indicators are $\mathbf 1_{\{\lambda \ge \|\beta\|\}}$ and $\infty\,\mathbf 1_{\{\lambda < \|\beta\|\}}$. The statement here is the first member of the chain equal to its last member, which is unaffected. Norms are in Theorem 2's convention (the page swaps $p$ and $q$). Values are in $[0,\infty]$.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, App. A.1, proof of Theorem 2, p. 30 (third display)

import Mathlib
import Definitions.Def_RWPI_Classif_losses

open scoped ENNReal

namespace RWPI.Classif

/-- App. A.1, proof of Theorem 2, p. 30 (the chain after the inner supremum): for labels
`Yᵢ ∈ {−1, +1}` and `δ ≥ 0`,
`inf_{λ ≥ 0} { δλ + (1/n) Σᵢ sup_x { log(1 + exp(−Yᵢβᵀx)) − λ‖x − Xᵢ‖_q } }
  = (1/n) Σᵢ log(1 + exp(−Yᵢβᵀ Xᵢ)) + δ‖β‖_p`. -/
theorem logistic_outer_min {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (hY : ∀ i, Y i = 1 ∨ Y i = -1) (p q : ℝ≥0∞) (hpq : p.HolderConjugate q)
    (β : Fin d → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    (⨅ (lam : ℝ) (_ : 0 ≤ lam), (ENNReal.ofReal (δ * lam) + (n : ℝ≥0∞)⁻¹ *
        ∑ i, ⨆ x : Fin d → ℝ, (ENNReal.ofReal (logLoss β (x, Y i)) -
          ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x - X i)‖))) =
      ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, logLoss β (X i, Y i) + δ * ‖WithLp.toLp p β‖) := by sorry

end RWPI.Classif
