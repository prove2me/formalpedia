-- Prove2me | Theorems.Thm_SubsetShrink_L2_eq_29
-- name    : SubsetShrink.L2.eq_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:19.788666+00:00
-- url     : https://prove2.me/theorems/cf6cce17-40fd-4898-b99f-76f8c5a99d51
-- title:
--   (29), p. 39 — the basic inequality for the ℓ2-regularized best-subsets estimator
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $f^*,\epsilon\in\mathbb R^n$, $y=f^*+\epsilon$, $k\in\mathbb N$ and $\lambda\in\mathbb R$. Let $\hat\beta_2$ be any $\ell_2$-regularized best-subsets solution of (16): $\|\hat\beta_2\|_0\le k$ and $\hat\beta_2$ minimizes $\|y-X\beta\|^2+\lambda\|\beta\|$ over $\|\beta\|_0\le k$. Then for every $\beta\in B_0(k)$,
--   $$\|y-X\hat\beta_2\|^2+\lambda\|\hat\beta_2\|\le\|y-X\beta\|^2+\lambda\|\beta\|,$$
--   and consequently
--   $$\|f^*-X\hat\beta_2\|^2+\lambda\|\hat\beta_2\|\le\|f^*-X\beta\|^2+2\epsilon^\top X(\hat\beta_2-\beta)+\lambda\|\beta\|.$$
--
--   This basic inequality is the starting point of both the slow-rate and the fast-rate bounds of Theorem 2: every later step controls the cross term $\epsilon^\top X(\hat\beta_2-\beta)$ on a noise event.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 39, proof of Theorem 2 (B.2), first display and (29)

import Mathlib
import Definitions.Def_SubsetShrink_L2_Model

namespace SubsetShrink.L2

/-- Proof of Theorem 2 (B.2), p. 39, first display and (29): for every ℓ2-regularized
best-subsets solution `βhat` of (16) with data `y = f* + ε` and every `β ∈ B0(k)`,
`‖y − Xβ̂₂‖² + λ‖β̂₂‖ ≤ ‖y − Xβ‖² + λ‖β‖`, and hence
`‖f* − Xβ̂₂‖² + λ‖β̂₂‖ ≤ ‖f* − Xβ‖² + 2ε⊤X(β̂₂ − β) + λ‖β‖`. -/
theorem eq_29 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ) (k : ℕ)
    (lam : ℝ) (βhat β : Fin p → ℝ)
    (hbest : IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat) (hβ : β ∈ B0 k) :
    (l2 (fun i => (fstar i + ε i) - X.mulVec βhat i) ^ 2 + lam * l2 βhat ≤
        l2 (fun i => (fstar i + ε i) - X.mulVec β i) ^ 2 + lam * l2 β) ∧
      l2 (resid X fstar βhat) ^ 2 + lam * l2 βhat ≤
        l2 (resid X fstar β) ^ 2 + 2 * dot ε (X.mulVec (βhat - β)) + lam * l2 β := by sorry

end SubsetShrink.L2
