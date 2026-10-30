-- Prove2me | Theorems.Thm_RetailerLedMarketplaces_CapacityAllocation_marketplace_operating_modes
-- name    : RetailerLedMarketplaces.CapacityAllocation.marketplace_operating_modes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:48:07.401189+00:00
-- url     : https://prove2.me/theorems/5afe9765-3fb0-4b27-95a1-1de7f69c3c6e
-- title:
--   Proposition 2 — capacity allocation and marketplace operating modes (corrected: pricing ties)
-- statement:
--   Fix $c\ge0$, $f\in[0,1]$, $\lambda\in[1/2,1]$ and an arbitrary probability distribution of products with density on $[c,\infty)$ and $G(c)=0$. There exists one threshold $\underline k\in[0,1]$, independent of capacity $k$, with
--
--   $$\underline k=1-G(v^*)\quad(f<1),\qquad\underline k=0\quad(f=1).$$
--
--   At $f=0$, the threshold equals one. For every $k\in[0,1]$ there is an assortment $A$ of mass exactly $k$ that maximizes actual extended retailer profit against every admissible measurable assortment and forms the selected sequential continuation with seller entry $E$. This includes optimal pricing after every quote, an optimal retailer response after every measurable seller history, and all sellers' unilateral entry inequalities. The complete pricing report gives the source prices, actual quantities and profits. The canonical quantile has tail mass $k$, is finite for positive $k$, is $+\infty$ at zero and $c$ at one. The retailer assortment is empty at zero capacity.
--
--   For $f<1$, sellers enter $E=[v_T,\infty)$. In Mode I, $k\le\underline k$, the retailer enters the upper tail at the source-consistent quantile representative $q_K\ge v_T$. This representative is the maximum of the canonical quantile and $v_T$; its tail agrees with the canonical tail modulo null products. Markets below $v_T$ are empty, $[v_T,q_K)$ is SBT and $[q_K,\infty)$ is SBMT. The zero-capacity case has an empty retailer tail.
--
--   In Mode II, $k>\underline k$, there are thresholds satisfying
--
--   $$c\le v_L\le v_T\le v_H\le v^*,\qquad A=[v_L,v_T)\cup[v_H,\infty),$$
--   $$v_L-c=\Delta(v_H),\qquad 1-G(v_H)+G(v_T)-G(v_L)=k.$$
--
--   The lower products $[c,v_L)$ are empty, followed by SBM, SBT and SBMT on the three successive intervals. At full capacity the selected thresholds are $v_L=c,v_H=v_T$.
--
--   For $f=1$, no sellers enter and the marketplace is foreclosed. The retailer enters the canonical upper tail, which is entirely SBM; remaining markets are empty. The extended thresholds satisfy $v_T=v_H=+\infty$ and $v_L=v_K$, including at zero cost. Positive capacity is the pure-SBM Mode II case; zero capacity is the empty equality case.
--
--   The result constructs a ranked optimum and its incentives. It does not assert uniqueness of every maximizer when distinct assortments can all have infinite aggregate profit.
--
--   Differences from the source:
--   - reading: firms entry choices ensure the stated configurations → existence of the source-selected sequential continuation, with pricing deviations and an optimal retailer plan at every measurable seller history; reason: indifference permits other entry and pricing selections, especially at lambda=1; uniqueness of all equilibria is not asserted
--   - encoding: a continuum with density g on [c,infinity) and G(c)=0 → a probability measure represented by a measurable nonnegative extended density and zero mass on (-infinity,c]; reason: the CDF is computed from that measure; this represents the same laws without full support or finite moments
--   - encoding: the inverse CDF and limiting foreclosure thresholds → an extended upper generalized inverse with canonical endpoints infinity at k=0 and c at k=1; Mode I uses the maximum of that cutoff and vT as an equivalent representative; reason: density gaps allow several cutoffs with the same tail up to null sets; a canonical full-capacity cutoff c may lie below vT, while the selected Mode-I representative must be at least vT
--   - encoding: the proof writes strict interior Mode-II cutoff inequalities → closed bounds c≤vL≤vT≤vH≤vstar and the endpoint vL=c,vH=vT when k=1; reason: the proposition includes full capacity, where the strict interior inequalities fail
--   - reading: at f=1 the marketplace is foreclosed and vT tends to infinity → explicit no-seller entry with vT=vH=infinity and vL=vK, including zero cost; reason: at c=0 the literal limit of c/(1-f) is zero; the stated foreclosure is implemented operationally as a zero-profit nonentry selection
--   - encoding: total retailer profit is the integral of product-market profits → nonnegative extended integrals of actual demand-based profits, with nonnegativity asserted separately; reason: infinite means are permitted; no nonintegrable real integral or infinity-minus-infinity is used
--   - correction: SBMT always allocates quantities lambda and 1-lambda → the split holds when pT<v; at a price tie M sells one unit and T sells zero; reason: c=1,f=1/2,lambda=3/4,v=2 gives pT=pM=2, so the source tie rule contradicts the printed generic split; the profit formulas remain unchanged
--   - encoding: the SBMT price is (lambda*v+c*(1-lambda))/(1-f*(1-lambda)) → the printed price unless its denominator is zero, when pT=v; reason: c=0,f=1,lambda=0,v=1 makes the printed ratio 0/0; the selected completion retains this viable case and satisfies the actual pricing incentives
-- source:
--   Hervas-Drane and Shelegia, Retailer-Led Marketplaces, Management Science, Articles in Advance (2025), doi:10.1287/mnsc.2023.00315, printed p. 7 (PDF p. 9), Proposition 2 and fee-one discussion; printed pp. 13–15 (PDF pp. 15–17), Appendix A proof

import Definitions.Def_RetailerLedMarketplaces_CapacityAllocation_Allocation

open MeasureTheory Set RetailerMarketplace.Entry
noncomputable section

namespace RetailerLedMarketplaces.CapacityAllocation

/-- Proposition 2 at a fixed fee, all capacities, arbitrary continuous densities and
extended aggregate profits. Sequential deviations and global retailer optimality are conclusions. -/
theorem marketplace_operating_modes (p : Parameters) (hsteer : 1 / 2 ≤ p.lam)
    (d : ProductLaw p.c) :
    ∃ kb : ℝ, kb ∈ Icc 0 1 ∧ kb = capacityThreshold p d ∧
      (p.f < 1 → kb = 1 - cdf d (crossoverReal p)) ∧
      (p.f = 0 → kb = 1) ∧ (p.f = 1 → kb = 0) ∧
      ∀ k ∈ Icc (0 : ℝ) 1, ∃ a : Set ℝ,
        IsEquilibrium p d k (sellerEntry p) a ∧
        RetailerOptimal p d k (sellerEntry p) a ∧
        d.measure a = ENNReal.ofReal k ∧
        (∀ v ∈ Ici p.c, PricingReport p v) ∧
        d.measure (upperTail p (capacityQuantile p d k)) = ENNReal.ofReal k ∧
        (k = 0 → a = ∅ ∧ capacityQuantile p d k = ⊤) ∧
        (k = 1 → capacityQuantile p d k = (p.c : EReal)) ∧
        (0 < k → ∃ q : ℝ, capacityQuantile p d k = (q : EReal) ∧
          p.c ≤ q ∧ cdf d q = 1 - k) ∧
        (p.f < 1 → sellerEntry p = Ici (sellerThresholdReal p) ∧
          (k ≤ kb → a = upperTail p (modeOneCutoff p d k) ∧
            (sellerThresholdReal p : EReal) ≤ modeOneCutoff p d k ∧
            SameProducts p d a (upperTail p (capacityQuantile p d k)) ∧
            ∀ v ∈ Ici p.c, configuration (sellerEntry p) a v =
              if v < sellerThresholdReal p then .empty
              else if (v : EReal) < modeOneCutoff p d k then .sbt else .sbmt) ∧
          (kb < k → ∃ l h : ℝ, ThresholdSystem p d k l h ∧
            a = modeTwoAssortment p l h ∧
            (k = 1 → l = p.c ∧ h = sellerThresholdReal p) ∧
            ∀ v ∈ Ici p.c, configuration (sellerEntry p) a v =
              if v < l then .empty else if v < sellerThresholdReal p then .sbm
              else if v < h then .sbt else .sbmt)) ∧
        (p.f = 1 → sellerEntry p = ∅ ∧ sellerThreshold p = ⊤ ∧
          a = upperTail p (capacityQuantile p d k) ∧
          (∃ vL vH : EReal, vL = capacityQuantile p d k ∧ vH = ⊤ ∧
            a = upperTail p vL ∧ upperTail p vH = ∅) ∧
          ∀ v ∈ Ici p.c, configuration (sellerEntry p) a v =
            if capacityQuantile p d k ≤ (v : EReal) then .sbm else .empty) := by sorry

end RetailerLedMarketplaces.CapacityAllocation
