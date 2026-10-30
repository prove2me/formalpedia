-- Prove2me | Theorems.Thm_RetailerLedMarketplaces_CapacityAllocation_marginal_profit
-- name    : RetailerLedMarketplaces.CapacityAllocation.marginal_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:46:27.454596+00:00
-- url     : https://prove2.me/theorems/68ec4eee-44d4-4557-b0dc-a9b61cecc306
-- title:
--   Appendix A — marginal profit (corrected: boundary positivity)
-- statement:
--   Let $c\ge0$, $0\le f<1$ and $1/2\le\lambda\le1$. Both pricing denominators are positive. The gain from entering a viable marketplace product, computed from its actual finite payoffs, is
--
--   $$\Delta(v)=\frac{(v-v_T)(1-f)(\lambda-f(1-\lambda))}{1-f(1-\lambda)}\ge0\qquad(v\ge v_T).$$
--
--   It vanishes at $v_T$, is strictly positive above $v_T$, and is strictly increasing on the viable domain. At fixed cost, valuation and steering, the displayed expression is nonincreasing in the fee over ordered fees below one for which the product is viable at the larger fee. The comparison is strict for distinct fees and $v>0$.
--
--   For every admissible product law and measurable seller and retailer sets in $[c,\infty)$, actual retailer payoffs are measurable and nonnegative. For the selected seller set $E$ and every measurable retailer set $A$ in the product space,
--
--   $$\Pi(E,A)=\Pi(E,\varnothing)+\int_A\left(\mathbf1_E(v)\Delta(v)+\mathbf1_{E^c}(v)(v-c)\right)\,d\mu(v).$$
--
--   All aggregate quantities are nonnegative extended integrals. Below $v_T$, incremental profit is the monopoly margin $v-c$. This identity connects the source's finite marginal calculation to its actual capacity objective even when aggregate profits are infinite.
--
--   Differences from the source:
--   - correction: the marginal gain is positive when lambda>f/(1+f) → zero at vT, strictly positive above vT, and nonnegative on the viable domain; reason: c=1,f=1/2,lambda=3/4,v=vT=2 satisfies the stated steering inequality but gives marginal gain zero
--   - encoding: the marginal gain decreases in the fee → nonincreasing for ordered fees on products viable at the larger fee, strictly decreasing when the fees differ and v>0; reason: at the allowed zero-cost zero-valuation boundary the gain is identically zero, so strict decrease there has no meaning
--   - encoding: a continuum with density g on [c,infinity) and G(c)=0 → a probability measure represented by a measurable nonnegative extended density and zero mass on (-infinity,c]; reason: the CDF is computed from that measure; this represents the same laws without full support or finite moments
--   - encoding: total retailer profit is the integral of product-market profits → nonnegative extended integrals of actual demand-based profits, with nonnegativity asserted separately; reason: infinite means are permitted; no nonintegrable real integral or infinity-minus-infinity is used
--   - encoding: the pricing statement describes viable seller markets and the paper solves a subgame-perfect game → explicit strategies at every real price and no-sale seller continuations in unviable off-path entry configurations; reason: a full continuation must evaluate unilateral entry and price deviations, including histories that do not occur at the selected equilibrium
-- source:
--   Hervas-Drane and Shelegia, Retailer-Led Marketplaces, Management Science, Articles in Advance (2025), doi:10.1287/mnsc.2023.00315, printed p. 14 (PDF p. 16), Appendix A, proof of Proposition 2, marginal-profit display

import Definitions.Def_RetailerLedMarketplaces_CapacityAllocation_Allocation

open MeasureTheory Set RetailerMarketplace.Entry
noncomputable section

namespace RetailerLedMarketplaces.CapacityAllocation
attribute [local instance] Classical.propDecidable

/-- Appendix A, proof of Proposition 2, marginal-profit display. Positivity is strict
above the entry boundary; the fee comparison includes its zero-cost boundary. -/
theorem marginal_profit (p : Parameters) (hsteer : 1 / 2 ≤ p.lam) (hfee : p.f < 1) :
    0 < 1 - p.f * (1 - p.lam) ∧ 0 < p.lam - p.f * (1 - p.lam) ∧
    (∀ v ∈ Ici (sellerThresholdReal p),
      entryGain p v = marginalFormula p.c p.f p.lam v ∧ 0 ≤ entryGain p v) ∧
    entryGain p (sellerThresholdReal p) = 0 ∧
    (∀ v : ℝ, sellerThresholdReal p < v → 0 < entryGain p v) ∧
    StrictMonoOn (entryGain p) (Ici (sellerThresholdReal p)) ∧
    (∀ f₁ f₂ v : ℝ, 0 ≤ f₁ → f₁ ≤ f₂ → f₂ < 1 → p.c ≤ (1 - f₂) * v →
      marginalFormula p.c f₂ p.lam v ≤ marginalFormula p.c f₁ p.lam v ∧
      (f₁ < f₂ → 0 < v → marginalFormula p.c f₂ p.lam v < marginalFormula p.c f₁ p.lam v)) ∧
    (∀ (d : ProductLaw p.c) (e a : Set ℝ), MeasurableSet e → e ⊆ Ici p.c →
      MeasurableSet a → a ⊆ Ici p.c →
      Measurable (fun v => outcomeM p v (decide (v ∈ a)) (decide (v ∈ e))) ∧
      (∀ v ∈ Ici p.c, 0 ≤ outcomeM p v (decide (v ∈ a)) (decide (v ∈ e)))) ∧
    ∀ (d : ProductLaw p.c) (a : Set ℝ), MeasurableSet a → a ⊆ Ici p.c →
      totalProfit p d (sellerEntry p) a = baselineProfit p d + incrementalProfit p d a := by sorry

end RetailerLedMarketplaces.CapacityAllocation
