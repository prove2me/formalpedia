-- Prove2me | Theorems.Thm_SubsetShrink_L2_g_display
-- name    : SubsetShrink.L2.g_display
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:27.849367+00:00
-- url     : https://prove2.me/theorems/508ccda4-a305-4b86-8110-46c47066da14
-- title:
--   p. 40, first fast-rate display — the basic inequality on the event G_2k
-- statement:
--   Let $X\in\mathbb R^{n\times p}$ have columns of unit Euclidean norm, let $\sigma>0$, $\delta_0\in(0,1]$, $1\le k\le p$, $\lambda\ge0$, $f^*,\epsilon\in\mathbb R^n$ and $y=f^*+\epsilon$. Suppose $\epsilon$ lies in the event $\mathcal G_{2k}$ (with parameter $\delta_0$) and $\hat\beta_2$ is any $\ell_2$-regularized best-subsets solution of (16). Then for every $\beta\in B_0(k)$,
--   $$\|f^*-X\hat\beta_2\|^2\le\|f^*-X\beta\|^2+2\sigma\big[10k\log(ep/[2k])+\log(1/\delta_0)\big]^{1/2}\big(\|f^*-X\hat\beta_2\|+\|f^*-X\beta\|\big)+\lambda\|\beta-\hat\beta_2\|.$$
--
--   This is the first step of the fast-rate bound of Theorem 2(B).
--
--   **Formalization Note** $\mathcal G_{2k}$ is the event $\mathcal G_s$ of p. 13, as printed, at $s=2k$; its term $5s\log(ep/s)$ equals $10k\log(ep/[2k])$ there. Since $2k\le 2p<ep$, the logarithm is positive.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 40, proof of Theorem 2 (B.2), first display of the fast rate

import Mathlib
import Definitions.Def_SubsetShrink_L2_Model

namespace SubsetShrink.L2

/-- Proof of Theorem 2 (B.2), p. 40, first display of the fast rate: on the event `G_2k`
(the printed `G_s` of p. 13 at `s = 2k`, with parameter `δ0 ∈ (0, 1]`), for every
ℓ2-regularized best-subsets solution `βhat` (16) with data `y = f* + ε`, `λ ≥ 0`, and every
`β ∈ B0(k)`,
`‖f* − Xβ̂₂‖² ≤ ‖f* − Xβ‖² + 2σ[10k log(ep/[2k]) + log(1/δ0)]^{1/2} (‖f* − Xβ̂₂‖ + ‖f* − Xβ‖)
  + λ‖β − β̂₂‖`.
Here `10k log(ep/[2k]) = 5(2k) log(ep/(2k))` is `G_s`'s `5s log(ep/s)` at `s = 2k`. -/
theorem g_display {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ)
    (σ δ0 : ℝ) (k : ℕ) (lam : ℝ) (βhat β : Fin p → ℝ)
    (hX : UnitCols X) (hσ : 0 < σ) (hk : 1 ≤ k) (hkp : k ≤ p)
    (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1) (hlam : 0 ≤ lam)
    (hG : ε ∈ G X σ δ0 (2 * k))
    (hbest : IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat) (hβ : β ∈ B0 k) :
    l2 (resid X fstar βhat) ^ 2 ≤
      l2 (resid X fstar β) ^ 2 +
        2 * σ * Real.sqrt (10 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (2 * (k : ℝ))) +
          Real.log (1 / δ0)) * (l2 (resid X fstar βhat) + l2 (resid X fstar β)) +
        lam * l2 (β - βhat) := by sorry

end SubsetShrink.L2
