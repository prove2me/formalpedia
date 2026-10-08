-- Prove2me | Theorems.Thm_RWPI_Classif_hinge_outer_min
-- name    : RWPI.Classif.hinge_outer_min
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:53:33.240006+00:00
-- url     : https://prove2.me/theorems/858dd531-d8cc-44ee-a25b-121851aacc89
-- title:
--   Proof of Theorem 2, p. 31 — the outer minimisation over λ for the hinge-loss SVM
-- statement:
--   Let $p, q \in [1,\infty]$ satisfy $1/p + 1/q = 1$. Let $(X_1,Y_1),\dots,(X_n,Y_n) \in \mathbb R^d \times \{-1,+1\}$ with $n \ge 1$, let $\beta \in \mathbb R^d$ and $\delta \ge 0$. Then
--
--   $$\inf_{\lambda \ge 0}\Big\{ \delta\lambda + \frac1n\sum_{i=1}^n \sup_{\Delta\in\mathbb R^d}\Big\{ \big(1 - Y_i\beta^T(X_i+\Delta)\big)^+ - \lambda\|\Delta\|_q \Big\}\Big\} = \frac1n\sum_{i=1}^n \big(1 - Y_i\beta^T X_i\big)^+ + \delta\,\|\beta\|_p .$$
--
--   The paper observes that it suffices to restrict the outer minimization to $\lambda \ge \|\beta\|_p$ (elsewhere the inner suprema are infinite) and evaluates the restricted infimum; the statement combines the two. With Proposition 1 the left-hand side is the worst-case expected hinge loss over $\{P : D_{N_q}(P,P_n)\le\delta\}$, so this is the per-$\beta$ form of the SVM half of Theorem 2.
--
--   **Formalization Note** Norms are in Theorem 2's convention (the page writes the threshold as $\|\beta\|_q$). Values are in $[0,\infty]$.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, App. A.1, proof of Theorem 2, p. 31 (display after 'it is sufficient to restrict to λ ≥ ‖β‖')

import Mathlib
import Definitions.Def_RWPI_Classif_losses

open scoped ENNReal

namespace RWPI.Classif

/-- App. A.1, proof of Theorem 2, p. 31: for labels `Yᵢ ∈ {−1, +1}` and `δ ≥ 0`, the outer
minimisation of the dual over `λ ≥ 0` (where it suffices to take `λ ≥ ‖β‖_p`) gives
`inf_{λ ≥ 0} { δλ + (1/n) Σᵢ sup_Δ { (1 − Yᵢβᵀ(Xᵢ + Δ))⁺ − λ‖Δ‖_q } }
  = (1/n) Σᵢ (1 − Yᵢβᵀ Xᵢ)⁺ + δ‖β‖_p`. -/
theorem hinge_outer_min {d n : ℕ} (hn : 0 < n) (X : Fin n → Fin d → ℝ) (Y : Fin n → ℝ)
    (hY : ∀ i, Y i = 1 ∨ Y i = -1) (p q : ℝ≥0∞) (hpq : p.HolderConjugate q)
    (β : Fin d → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    (⨅ (lam : ℝ) (_ : 0 ≤ lam), (ENNReal.ofReal (δ * lam) + (n : ℝ≥0∞)⁻¹ *
        ∑ i, ⨆ Δ : Fin d → ℝ, (ENNReal.ofReal (hingeLoss β (X i + Δ, Y i)) -
          ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q Δ‖))) =
      ENNReal.ofReal ((1 / (n : ℝ)) * ∑ i, hingeLoss β (X i, Y i) + δ * ‖WithLp.toLp p β‖) := by sorry

end RWPI.Classif
