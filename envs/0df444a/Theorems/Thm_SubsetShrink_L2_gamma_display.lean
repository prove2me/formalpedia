-- Prove2me | Theorems.Thm_SubsetShrink_L2_gamma_display
-- name    : SubsetShrink.L2.gamma_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:35.47077+00:00
-- url     : https://prove2.me/theorems/6297f923-64bc-49a1-a9f8-6f67bdb533cb
-- title:
--   p. 40 — bounding λ‖β − β̂₂‖ through the sparse eigenvalue γ_2k
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $f^*\in\mathbb R^n$, $k\in\mathbb N$, $\lambda\ge0$, and suppose the minimal $2k$-sparse eigenvalue $\gamma_{2k}$ of $X$ is positive. Then for all $\beta,\hat\beta_2\in B_0(k)$,
--   $$\lambda\|\beta-\hat\beta_2\|\le\gamma_{2k}^{-1}\lambda\|X(\beta-\hat\beta_2)\|\le\gamma_{2k}^{-1}\lambda\big(\|f^*-X\hat\beta_2\|+\|f^*-X\beta\|\big).$$
--
--   In the proof of Theorem 2(B) this converts the penalty term of the fast-rate display into prediction errors, which produces the term $\gamma_{2k}^{-2}\lambda^2$ of the fast rate.
--
--   **Formalization Note** The statement assumes $\gamma_{2k}>0$; with $\gamma_{2k}=0$ the paper's $\gamma_{2k}^{-1}$ is infinite, while Lean's $0^{-1}=0$ would make the inequality false.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 40, proof of Theorem 2 (B.2), display bounding the last term

import Mathlib
import Definitions.Def_SubsetShrink_L2_Model

namespace SubsetShrink.L2

/-- Proof of Theorem 2 (B.2), p. 40: for `γ_2k > 0`, `λ ≥ 0` and `β, β̂₂ ∈ B0(k)`,
`λ‖β − β̂₂‖ ≤ γ_2k⁻¹ λ ‖X(β − β̂₂)‖ ≤ γ_2k⁻¹ λ (‖f* − Xβ̂₂‖ + ‖f* − Xβ‖)`. -/
theorem gamma_display {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ)
    (k : ℕ) (lam : ℝ) (βhat β : Fin p → ℝ)
    (hγ : 0 < gam X (2 * k)) (hlam : 0 ≤ lam) (hβhat : βhat ∈ B0 k) (hβ : β ∈ B0 k) :
    lam * l2 (β - βhat) ≤ (gam X (2 * k))⁻¹ * lam * l2 (X.mulVec (β - βhat)) ∧
      (gam X (2 * k))⁻¹ * lam * l2 (X.mulVec (β - βhat)) ≤
        (gam X (2 * k))⁻¹ * lam * (l2 (resid X fstar βhat) + l2 (resid X fstar β)) := by sorry

end SubsetShrink.L2
