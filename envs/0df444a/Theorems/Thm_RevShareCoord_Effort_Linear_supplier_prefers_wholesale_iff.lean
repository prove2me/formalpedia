-- Prove2me | Theorems.Thm_RevShareCoord_Effort_Linear_supplier_prefers_wholesale_iff
-- name    : RevShareCoord.Effort.Linear.supplier_prefers_wholesale_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:06:14.085376+00:00
-- url     : https://prove2.me/theorems/29f23a4a-3fa5-43d8-ba24-0eba4b3432d9
-- title:
--   Sec. 4.2.2, p. 24 — the supplier's optimal profit V(φ) = (1 − c)²/(4(1 + φ(1 − 2τ²))) increases in φ iff τ > 1/√2
-- statement:
--   In the linear example with inverse demand $P(q, e) = 1 - q + 2\tau e$ and effort cost $e^2$, let $0 \le \tau < 1$ and $0 < c < 1$. For a revenue share $\phi \in (0, 1]$ let $V(\phi)$ be the supplier's optimal profit: the supremum, over wholesale prices $w \ge 0$, of $(1-\phi)R(q, e) + q(w - c)$, where $(q, e)$ is the retailer's optimal response to $\{\phi, w\}$ over $q, e \ge 0$. Then:
--
--   1. for every $\phi \in (0, 1]$ the supremum is attained, at the wholesale price $w(\phi) = \phi\big((1-\tau^2)\phi + c(1-\phi\tau^2)\big)/\big(1 + \phi(1-2\tau^2)\big) \ge 0$, and
--   $$
--   V(\phi) = \frac{(1 - c)^2}{4\big(1 + \phi(1 - 2\tau^2)\big)} ;
--   $$
--   2. if $\tau > 1/\sqrt 2$, $V$ is strictly increasing on $(0, 1]$, so the wholesale-price contract $\phi = 1$ is the supplier's unique optimal share;
--   3. if $\tau = 1/\sqrt 2$, $V(\phi) = (1-c)^2/4$ for every $\phi \in (0, 1]$;
--   4. if $\tau < 1/\sqrt 2$, $V$ is strictly decreasing on $(0, 1]$ and $V(\phi) \to (1-c)^2/4$ as $\phi \to 0^+$.
--
--   When retail effort has a strong effect on demand the supplier prefers a smaller share of a larger pie and offers the plain wholesale-price contract; when effort matters little she prefers to keep as much revenue as possible.
--
--   **Formalization Note.** The page says "otherwise the supplier's profit is decreasing in $\phi$", which fails at $\tau = 1/\sqrt 2$, where $V$ is constant; the trichotomy is stated instead. The page's optimal share "$\phi = 0$" for $\tau < 1/\sqrt 2$ lies outside the model (the retailer's order $q(w,\phi)$ divides by $\phi$, and with $\phi = 0$ the retailer keeps no revenue), so it is stated as strict decrease on $(0,1]$ together with the limit at $0^+$, which is the supremum and is not attained. $\tau = 1$ is excluded as in the integrated problem, and $c < 1$ makes the integrated quantity positive. The retailer's response is the joint maximizer over $q, e \ge 0$, and the supplier's value is defined from the set of attainable profits, not from the printed formula for $w(\phi)$.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 24 (PDF p. 25), Section 4.2.2, from 'Returning to the decentralized system' to 'a revenue-sharing contract with φ = 0'

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

namespace RevShareCoord.Effort.Linear

/-- Sec. 4.2.2, p. 24 (goal): the supplier's optimal profit with share `φ ∈ (0, 1]` is
`V(φ) = (1 − c)²/(4(1 + φ(1 − 2τ²)))`, attained at the wholesale price `w(φ)`. `V` is strictly
increasing on `(0, 1]` if `τ > 1/√2` (so the wholesale-price contract `φ = 1` is optimal),
constant if `τ = 1/√2`, and strictly decreasing if `τ < 1/√2`, with supremum the limit
`(1 − c)²/4` as `φ → 0⁺`. -/
theorem supplier_prefers_wholesale_iff (τ c : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hc0 : 0 < c) (hc1 : c < 1) :
    (∀ φ ∈ Set.Ioc (0 : ℝ) 1,
      IsGreatest (supplierOutcomes τ c φ) ((1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2)))) ∧
      supplierValue τ c φ = (1 - c) ^ 2 / (4 * (1 + φ * (1 - 2 * τ ^ 2))) ∧
      0 ≤ wholesalePrice τ c φ ∧
      (∃ x : ℝ × ℝ, IsRetailerResponse τ φ (wholesalePrice τ c φ) x) ∧
      (∀ x : ℝ × ℝ, IsRetailerResponse τ φ (wholesalePrice τ c φ) x →
        supplierProfit τ c φ (wholesalePrice τ c φ) x.1 x.2 = supplierValue τ c φ)) ∧
    (1 / Real.sqrt 2 < τ →
      StrictMonoOn (supplierValue τ c) (Set.Ioc 0 1) ∧
      ∀ φ ∈ Set.Ioo (0 : ℝ) 1, supplierValue τ c φ < supplierValue τ c 1) ∧
    (τ = 1 / Real.sqrt 2 → ∀ φ ∈ Set.Ioc (0 : ℝ) 1, supplierValue τ c φ = (1 - c) ^ 2 / 4) ∧
    (τ < 1 / Real.sqrt 2 →
      StrictAntiOn (supplierValue τ c) (Set.Ioc 0 1) ∧
      Filter.Tendsto (supplierValue τ c) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 - c) ^ 2 / 4))) := by sorry

end RevShareCoord.Effort.Linear
