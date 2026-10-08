-- Prove2me | Theorems.Thm_RevShareCoord_Effort_Linear_optimal_wholesale_price
-- name    : RevShareCoord.Effort.Linear.optimal_wholesale_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:06:00.632822+00:00
-- url     : https://prove2.me/theorems/88323dbf-e685-438f-8c53-0a76def5ad24
-- title:
--   Sec. 4.2.2, p. 24 — π_s(w, φ) is concave in w and w(φ) is the supplier's unique optimal wholesale price
-- statement:
--   In the linear example, let $0 \le \tau < 1$, $0 < c < 1$ and $0 < \phi \le 1$, and let $\pi_s(w, \phi)$ be the supplier's profit when the retailer responds optimally to $\{\phi, w\}$. Then:
--
--   1. $w \mapsto \pi_s(w, \phi)$ is strictly concave on $w \le \phi$, with second derivative
--   $$
--   \frac{\partial^2 \pi_s(w,\phi)}{\partial w^2} = -\frac{1 + \phi(1 - 2\tau^2)}{2\phi^2(1 - \phi\tau^2)^2} < 0 \qquad (w < \phi);
--   $$
--   2. the wholesale price
--   $$
--   w(\phi) = \frac{\phi\big((1-\tau^2)\phi + c(1 - \phi\tau^2)\big)}{1 + \phi(1 - 2\tau^2)}
--   $$
--   satisfies $0 \le w(\phi) < \phi$ and is the unique maximizer of $\pi_s(\cdot, \phi)$ over $w \ge 0$.
--
--   For each share $\phi$ this is the supplier's best wholesale price, and since $w(\phi) < \phi$ the retailer orders a positive quantity.
--
--   **Formalization Note.** The page prints the numerator of the second derivative as $1 - \phi(1 - 2\tau^2)$; direct differentiation gives $1 + \phi(1 - 2\tau^2)$, which is what is stated (both are positive for $\tau < 1$, $\phi \in (0,1]$, so the page's conclusions stand). The page calls $\pi_s$ concave in $w$; for $w \ge \phi$ the retailer orders nothing and $\pi_s = 0$, so $\pi_s$ is concave only on $w \le \phi$, and the optimum is taken over all $w \ge 0$.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 24 (PDF p. 25), Section 4.2.2, 'The supplier's profit is concave in w, ∂²π_s(w, φ)/∂w² = … < 0, so the optimal wholesale price is w(φ) = …'

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

namespace RevShareCoord.Effort.Linear

/-- Sec. 4.2.2, p. 24: for a share `φ ∈ (0, 1]`, the supplier's profit `π_s(w, φ)` is strictly
concave in `w` on `w ≤ φ` with second derivative `−(1 + φ(1 − 2τ²))/(2φ²(1 − φτ²)²)` (sign of the
printed numerator corrected), and `w(φ)` is its unique maximizer over `w ≥ 0`, with
`0 ≤ w(φ) < φ`. -/
theorem optimal_wholesale_price (τ c φ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) :
    StrictConcaveOn ℝ (Set.Iic φ) (supplierProfitAt τ c φ) ∧
    (∀ w : ℝ, w < φ → iteratedDeriv 2 (supplierProfitAt τ c φ) w =
      -(1 + φ * (1 - 2 * τ ^ 2)) / (2 * φ ^ 2 * (1 - φ * τ ^ 2) ^ 2)) ∧
    0 ≤ wholesalePrice τ c φ ∧ wholesalePrice τ c φ < φ ∧
    IsMaxOn (supplierProfitAt τ c φ) (Set.Ici 0) (wholesalePrice τ c φ) ∧
    (∀ w : ℝ, 0 ≤ w → IsMaxOn (supplierProfitAt τ c φ) (Set.Ici 0) w →
      w = wholesalePrice τ c φ) := by sorry

end RevShareCoord.Effort.Linear
