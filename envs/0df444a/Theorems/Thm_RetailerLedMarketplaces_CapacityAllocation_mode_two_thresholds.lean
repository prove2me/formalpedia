-- Prove2me | Theorems.Thm_RetailerLedMarketplaces_CapacityAllocation_mode_two_thresholds
-- name    : RetailerLedMarketplaces.CapacityAllocation.mode_two_thresholds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:47:15.321636+00:00
-- url     : https://prove2.me/theorems/cc92a9d6-44aa-4aac-8777-796a2f9d607e
-- title:
--   Appendix A — threshold system (corrected: uniqueness and endpoints)
-- statement:
--   Let $c\ge0$, $0\le f<1$, $1/2\le\lambda\le1$ and $k\in[0,1]$ exceed $\underline k=1-G(v^*)$. There exist $c\le v_L\le v_T\le v_H\le v^*$ satisfying
--
--   $$v_L-c=\Delta(v_H),\qquad (1-G(v_H))+(G(v_T)-G(v_L))=k.$$
--
--   The assortment $A=[v_L,v_T)\cup[v_H,\infty)$ uses mass exactly $k$, dominates every feasible measurable retailer assortment, and participates in the selected sequential continuation, including optimal responses at every measurable seller history. Markets below $v_L$ are empty; the successive intervals $[v_L,v_T)$, $[v_T,v_H)$ and $[v_H,\infty)$ have configurations SBM, SBT and SBMT.
--
--   Any two solutions of the system induce the same assortment modulo null products. If the CDF is strictly increasing on $[c,\infty)$, the numerical solutions also coincide; strict increase is a condition only of this additional conclusion. At $k=1$, the selected thresholds are $v_L=c,v_H=v_T$, and the capacity expression equals one.
--
--   This retains existence, both equalization equations and global optimality under density gaps, and supplies the Mode II clause needed by Proposition 2.
--
--   Differences from the source:
--   - correction: the two equations identify unique numerical thresholds → solutions exist and their induced assortments agree modulo null sets; numerical uniqueness is conditional on a strictly increasing CDF; reason: c=1,f=1/2,lambda=1,k=3/4 and density 1 on [1,5/4] and [7/4,2], density 1/2 on [4,5], admit both (vL,vH)=(3/2,3) and (13/8,13/4)
--   - correction: the capacity expression at vH=vT,vL=c equals 1-G(vT) → the endpoint capacity expression equals 1; reason: with c=1,f=1/2,lambda=1 and shifted unit exponential G, the printed bound at k=1/2 is exp(-1)≥1/2, which is false; the displayed system itself is unchanged
--   - encoding: the proof writes strict interior Mode-II cutoff inequalities → closed bounds c≤vL≤vT≤vH≤vstar and the endpoint vL=c,vH=vT when k=1; reason: the proposition includes full capacity, where the strict interior inequalities fail
--   - encoding: a continuum with density g on [c,infinity) and G(c)=0 → a probability measure represented by a measurable nonnegative extended density and zero mass on (-infinity,c]; reason: the CDF is computed from that measure; this represents the same laws without full support or finite moments
--   - encoding: total retailer profit is the integral of product-market profits → nonnegative extended integrals of actual demand-based profits, with nonnegativity asserted separately; reason: infinite means are permitted; no nonintegrable real integral or infinity-minus-infinity is used
--   - reading: firms entry choices ensure the stated configurations → existence of the source-selected sequential continuation, with pricing deviations and an optimal retailer plan at every measurable seller history; reason: indifference permits other entry and pricing selections, especially at lambda=1; uniqueness of all equilibria is not asserted
-- source:
--   Hervas-Drane and Shelegia, Retailer-Led Marketplaces, Management Science, Articles in Advance (2025), doi:10.1287/mnsc.2023.00315, printed p. 15 (PDF p. 17), Appendix A, proof of Proposition 2, threshold-system display

import Definitions.Def_RetailerLedMarketplaces_CapacityAllocation_Allocation

open MeasureTheory Set RetailerMarketplace.Entry
noncomputable section

namespace RetailerLedMarketplaces.CapacityAllocation

/-- Appendix A, threshold-system display. Numerical uniqueness is conditional;
without full support the allocation, not the pair of numbers, is unique modulo null sets. -/
theorem mode_two_thresholds (p : Parameters) (hsteer : 1 / 2 ≤ p.lam) (hfee : p.f < 1)
    (d : ProductLaw p.c) (k : ℝ) (hk : k ∈ Icc 0 1) (hmode : capacityThreshold p d < k) :
    (∃ l h : ℝ, ThresholdSystem p d k l h ∧
      d.measure (modeTwoAssortment p l h) = ENNReal.ofReal k ∧
      RetailerOptimal p d k (sellerEntry p) (modeTwoAssortment p l h) ∧
      IsEquilibrium p d k (sellerEntry p) (modeTwoAssortment p l h) ∧
      (k = 1 → l = p.c ∧ h = sellerThresholdReal p) ∧
      ∀ v ∈ Ici p.c, configuration (sellerEntry p) (modeTwoAssortment p l h) v =
        if v < l then .empty else if v < sellerThresholdReal p then .sbm
        else if v < h then .sbt else .sbmt) ∧
    (∀ l h l' h' : ℝ, ThresholdSystem p d k l h → ThresholdSystem p d k l' h' →
      SameProducts p d (modeTwoAssortment p l h) (modeTwoAssortment p l' h') ∧
      (StrictMonoOn (cdf d) (Ici p.c) → l = l' ∧ h = h')) ∧
    (k = 1 → ThresholdSystem p d k p.c (sellerThresholdReal p) ∧
      (1 - cdf d (sellerThresholdReal p)) +
        (cdf d (sellerThresholdReal p) - cdf d p.c) = 1) := by sorry

end RetailerLedMarketplaces.CapacityAllocation
