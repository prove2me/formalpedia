-- Prove2me | Theorems.Thm_RetailerLedMarketplaces_CapacityAllocation_crossover
-- name    : RetailerLedMarketplaces.CapacityAllocation.crossover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:46:48.176444+00:00
-- url     : https://prove2.me/theorems/01a5bb02-63b4-4541-a110-ac4943ac26e0
-- title:
--   Appendix A, (A.2) — crossover (corrected: zero-cost strictness)
-- statement:
--   Let $c\ge0$, $0\le f<1$, $1/2\le\lambda\le1$ and let $G$ be any admissible product distribution. Then
--
--   $$v^*=\frac{c\lambda}{(1-f)^2(\lambda-f(1-\lambda))},\qquad c\le v_T\le v^*,\qquad\Delta(v^*)=v_T-c.$$
--
--   Strict inequality $v^*>v_T$ holds exactly when both cost and fee are positive. Every $v\ge v^*$ has a strictly greater marketplace entry gain than the monopoly margin of any product $c\le u<v_T$. At zero fee, $v^*=v_T=c$; at zero cost both thresholds are zero.
--
--   The capacity threshold and the associated tail satisfy
--
--   $$\underline k=1-G(v^*)\in[0,1],\qquad\mu([v^*,\infty))=\underline k.$$
--
--   At zero fee or zero cost, $\underline k=1$. Every canonical quantile has tail mass $k$ for $k\in[0,1]$; it is finite with $G(v_K)=1-k$ and $v_K\ge c$ for $k>0$, equals $+\infty$ at zero capacity, and equals $c$ at full capacity.
--
--   This supplies the crossover and capacity threshold used to separate the two allocation modes, without applying the formula at fee one.
--
--   Differences from the source:
--   - correction: vstar>vT whenever f>0 → vstar>vT exactly when c>0 and f>0, with weak order for all allowed costs; reason: c=0,f=1/2,lambda=3/4 gives vstar=vT=0 under the source formula
--   - encoding: a continuum with density g on [c,infinity) and G(c)=0 → a probability measure represented by a measurable nonnegative extended density and zero mass on (-infinity,c]; reason: the CDF is computed from that measure; this represents the same laws without full support or finite moments
--   - encoding: the inverse CDF vK=G inverse of 1-k → an extended upper generalized inverse with canonical endpoints infinity at k=0 and c at k=1; reason: a density need not give a strictly increasing CDF; the right endpoint of a quantile plateau has the required tail mass, with explicit choices at zero and full capacity
-- source:
--   Hervas-Drane and Shelegia, Retailer-Led Marketplaces, Management Science, Articles in Advance (2025), doi:10.1287/mnsc.2023.00315, printed p. 14 (PDF p. 16), Appendix A, crossover display and (A.2); printed p. 7 (PDF p. 9), (3)

import Definitions.Def_RetailerLedMarketplaces_CapacityAllocation_Allocation

open MeasureTheory Set RetailerMarketplace.Entry
noncomputable section

namespace RetailerLedMarketplaces.CapacityAllocation

/-- Appendix A, crossover display and (A.2), with (3)'s endpoint-safe quantiles.
Positive-fee strictness additionally needs positive cost, as the zero-cost example shows. -/
theorem crossover (p : Parameters) (hsteer : 1 / 2 ≤ p.lam) (hfee : p.f < 1)
    (d : ProductLaw p.c) :
    crossoverReal p = p.c * p.lam / ((1 - p.f) ^ 2 * (p.lam - p.f * (1 - p.lam))) ∧
    p.c ≤ sellerThresholdReal p ∧ sellerThresholdReal p ≤ crossoverReal p ∧
    entryGain p (crossoverReal p) = piSBM p.c (sellerThresholdReal p) ∧
    (sellerThresholdReal p < crossoverReal p ↔ 0 < p.c ∧ 0 < p.f) ∧
    (∀ v u : ℝ, crossoverReal p ≤ v → u ∈ Ico p.c (sellerThresholdReal p) →
      piSBM p.c u < entryGain p v) ∧
    (p.f = 0 → crossoverReal p = p.c ∧ sellerThresholdReal p = p.c) ∧
    (p.c = 0 → crossoverReal p = 0 ∧ sellerThresholdReal p = 0) ∧
    capacityThreshold p d = 1 - cdf d (crossoverReal p) ∧
    capacityThreshold p d ∈ Icc 0 1 ∧
    d.measure (Ici (crossoverReal p)) = ENNReal.ofReal (capacityThreshold p d) ∧
    (p.f = 0 ∨ p.c = 0 → capacityThreshold p d = 1) ∧
    capacityQuantile p d 0 = ⊤ ∧ capacityQuantile p d 1 = (p.c : EReal) ∧
    ∀ k ∈ Icc (0 : ℝ) 1,
      d.measure (upperTail p (capacityQuantile p d k)) = ENNReal.ofReal k ∧
      (0 < k → ∃ q : ℝ, capacityQuantile p d k = (q : EReal) ∧ p.c ≤ q ∧
        cdf d q = 1 - k) := by sorry

end RetailerLedMarketplaces.CapacityAllocation
