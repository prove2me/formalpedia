-- Prove2me | Theorems.Thm_RetailerLedMarketplaces_CapacityAllocation_pricing_continuation
-- name    : RetailerLedMarketplaces.CapacityAllocation.pricing_continuation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:44:40.104833+00:00
-- url     : https://prove2.me/theorems/86e251ac-109e-4a78-99d3-9c4f5047c4b3
-- title:
--   Proposition 1 — sequential pricing (corrected: tie quantities)
-- statement:
--   Fix $c\ge0$, $f\in[0,1]$, $\lambda\in[0,1]$ and a product $v\ge c$. The explicit pricing strategies form a sequentially rational continuation in every entry configuration. Each retailer response is optimal at every possible seller quote, and the seller's selected quote is optimal given that response strategy.
--
--   In SBM, the retailer charges $v$, steers to himself, sells one unit and earns $v-c$; the absent seller earns zero. For a viable seller, $(1-f)v\ge c$, SBT charges $p_T=v$, steers to the seller, sells one unit and gives profits $fv$ to the retailer and $(1-f)v-c$ to the seller. In SBMT the selected retailer response is $(p_M,S)=(v,M)$, the seller quotes the safely completed $\bar p_T$, and
--
--   $$\pi_M=\lambda(v-c)+(1-\lambda)f\bar p_T,\qquad \pi_T=(1-\lambda)((1-f)\bar p_T-c).$$
--
--   The seller price is at most $v$. When $\bar p_T<v$, quantities are $(\lambda,1-\lambda)$; at equality they are $(1,0)$. For unviable off-path seller entry, the seller has no sales and earns zero in either configuration; the retailer earns zero in SBT and $v-c$ in SBMT. All actual continuation profits are nonnegative on the product space.
--
--   This supplies the full pricing layer for entry incentives, including zero cost and all steering and fee endpoints, without claiming uniqueness of every pricing equilibrium.
--
--   Differences from the source:
--   - correction: SBMT always allocates quantities lambda and 1-lambda → the split holds when pT<v; at a price tie M sells one unit and T sells zero; reason: c=1,f=1/2,lambda=3/4,v=2 gives pT=pM=2, so the source tie rule contradicts the printed generic split; the profit formulas remain unchanged
--   - encoding: the SBMT price is (lambda*v+c*(1-lambda))/(1-f*(1-lambda)) → the printed price unless its denominator is zero, when pT=v; reason: c=0,f=1,lambda=0,v=1 makes the printed ratio 0/0; the selected completion retains this viable case and satisfies the actual pricing incentives
--   - encoding: the pricing statement describes viable seller markets and the paper solves a subgame-perfect game → explicit strategies at every real price and no-sale seller continuations in unviable off-path entry configurations; reason: a full continuation must evaluate unilateral entry and price deviations, including histories that do not occur at the selected equilibrium
--   - reading: Proposition 1 describes equilibrium outcomes in each entry configuration → the explicit selected pricing strategies satisfy sequential deviation inequalities and the stated outcome report; reason: the proof selects the high retailer price at indifference; other equilibrium selections need not have the same outcomes
-- source:
--   Hervas-Drane and Shelegia, Retailer-Led Marketplaces, Management Science, Articles in Advance (2025), doi:10.1287/mnsc.2023.00315, printed p. 5 (PDF p. 7), Proposition 1; printed p. 13 (PDF p. 15), proof of Proposition 1

import Definitions.Def_RetailerLedMarketplaces_CapacityAllocation_Allocation

open MeasureTheory Set RetailerMarketplace.Entry
noncomputable section

namespace RetailerLedMarketplaces.CapacityAllocation

/-- Proposition 1, including actual tie quantities, the singular price completion and
unviable off-path entry configurations. The steering domain is the full [0,1]. -/
theorem pricing_continuation (p : Parameters) :
    ∀ v ∈ Ici p.c, PricingReport p v := by sorry

end RetailerLedMarketplaces.CapacityAllocation
