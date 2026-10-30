-- Prove2me | Theorems.Thm_RetailerLedMarketplaces_CapacityAllocation_seller_entry
-- name    : RetailerLedMarketplaces.CapacityAllocation.seller_entry
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:45:27.840172+00:00
-- url     : https://prove2.me/theorems/29d4b26f-f30a-4ec5-a2d3-a268934fba69
-- title:
--   Lemma 1 — selected optimal seller entry (corrected: pricing ties)
-- statement:
--   Fix common cost $c\ge0$, fee $f\in[0,1]$ and steering share $\lambda\in[0,1]$. The selected entry set is measurable, lies in the product space, and satisfies
--
--   $$E=[v_T,\infty),\quad v_T=\frac c{1-f}\quad(f<1),\qquad E=\varnothing,\quad v_T=+\infty\quad(f=1).$$
--
--   The complete pricing report holds in every product market. An entering seller's profit is nonnegative under either retailer entry choice. Outside $E$, any deviating entry followed by the selected pricing continuation earns zero. For every retailer response plan, a seller cannot improve her actual payoff by changing entry and receiving the response specified at the resulting history. Entry at the ordinary zero-profit threshold and nonentry at fee one are the selected decisions; sellers can be indifferent.
--
--   This establishes entry incentives independently of how the retailer reallocates capacity after a seller deviation. The goal theorem separately constructs a plan optimal at every measurable history, so such optimality is not assumed here.
--
--   Differences from the source:
--   - reading: T enters products at or above vT and stays out elsewhere → the selected entry policy satisfies each seller deviation inequality for every retailer response plan; reason: the source no-entry-deterrence property makes entry incentives independent of the retailer choice; an optimal retailer plan is constructed separately in the allocation results
--   - reading: at f=1 the marketplace is foreclosed and vT tends to infinity → the selected seller-entry set is empty and the extended seller threshold is infinity, including at zero cost; reason: at c=0 the literal limit of c/(1-f) is zero; foreclosure is implemented as the permitted zero-profit nonentry selection
--   - encoding: the pricing statement describes viable seller markets and the paper solves a subgame-perfect game → explicit strategies at every real price and no-sale seller continuations in unviable off-path entry configurations; reason: a full continuation must evaluate unilateral entry and price deviations, including histories that do not occur at the selected equilibrium
--   - correction: SBMT always allocates quantities lambda and 1-lambda → the split holds when pT<v; at a price tie M sells one unit and T sells zero; reason: c=1,f=1/2,lambda=3/4,v=2 gives pT=pM=2, so the source tie rule contradicts the printed generic split; the profit formulas remain unchanged
--   - encoding: the SBMT price is (lambda*v+c*(1-lambda))/(1-f*(1-lambda)) → the printed price unless its denominator is zero, when pT=v; reason: c=0,f=1,lambda=0,v=1 makes the printed ratio 0/0; the selected completion retains this viable case and satisfies the actual pricing incentives
-- source:
--   Hervas-Drane and Shelegia, Retailer-Led Marketplaces, Management Science, Articles in Advance (2025), doi:10.1287/mnsc.2023.00315, printed p. 6 (PDF p. 8), Lemma 1 and (1)

import Definitions.Def_RetailerLedMarketplaces_CapacityAllocation_Allocation

open MeasureTheory Set RetailerMarketplace.Entry
noncomputable section

namespace RetailerLedMarketplaces.CapacityAllocation

/-- Lemma 1: the selected entry is incentive compatible against every retailer response
plan, hence also against the optimal plan constructed in Proposition 2. No optimality
of a plan is assumed or concealed in the entry-set definition. -/
theorem seller_entry (p : Parameters) :
    MeasurableSet (sellerEntry p) ∧ sellerEntry p ⊆ Ici p.c ∧
    (p.f < 1 → sellerEntry p = Ici (sellerThresholdReal p)) ∧
    (p.f = 1 → sellerEntry p = ∅ ∧ sellerThreshold p = ⊤) ∧
    (∀ v ∈ Ici p.c, PricingReport p v) ∧
    (∀ v ∈ sellerEntry p, ∀ m : Bool, 0 ≤ outcomeT p v m true) ∧
    (∀ v ∈ Ici p.c, v ∉ sellerEntry p → ∀ m : Bool, outcomeT p v m true = 0) ∧
    ∀ plan : Set ℝ → Set ℝ, SellerStable p (sellerEntry p) (plan (sellerEntry p)) plan := by sorry

end RetailerLedMarketplaces.CapacityAllocation
