-- Prove2me | Theorems.Thm_ReusablePricingAudit_FullModel_full_strength_static_pricing
-- name    : ReusablePricingAudit.FullModel.full_strength_static_pricing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:50:56.13334+00:00
-- url     : https://prove2.me/theorems/460d6aed-f4a1-4973-86ef-22f2a44549bd
-- title:
--   Theorem 1 — one static price achieves 15/19 of all three metrics
-- statement:
--   Fix any resource instance with $C\ge1$, $\mu,\Lambda,c>0$, concave net arrival reward, inverse demand on the full continuous rate domain, and nonnegative normalized objective weights. From any initial free inventory $q_0\in\{0,\ldots,C\}$, let $\pi^*$ be a chosen policy that is globally optimal against every admissible non-anticipating, possibly randomized policy.
--
--   There exists one admissible constant rate $l\in[0,\Lambda]$, hence one static pricing policy $\pi^s$, such that simultaneously
--   $$\mathcal P^{\pi^s}\ge\frac{15}{19}\mathcal P^{\pi^*},\qquad
--   \mathcal{MS}^{\pi^s}\ge\frac{15}{19}\mathcal{MS}^{\pi^*},\qquad
--   \mathcal{SL}^{\pi^s}\ge\frac{15}{19}\mathcal{SL}^{\pi^*}.$$
--   The constant rate can depend on the instance and comparator. Its three inequalities are unconditional: profits may be negative and any objective weight may be zero. The metrics are the expected long-run liminf quantities of the actual loss process, and market share is an accepted-sales rate without normalization by $\Lambda$.
--
--   This is the paper's full simultaneous static-price guarantee. It does not prescribe the particular rate in Eq. (9). The premise specifies a chosen global optimizer; existence of an optimizer is not an instance field or an additional claimed attainment theorem. Ratios follow when their denominators are positive.
--
--   Differences from the source:
--   - reading: the prose component guarantee is called equivalent to a display of three ratios → all three unconditional component inequalities, including zero and signed benchmark metrics; reason: at a service-optimal zero rate both profit and sales vanish; at C=μ=Λ=c=1, uniform demand and market-share weights the optimal rate 1 has profit -1/2, so the advertised fixed-price formulations are not equivalent
--   - reading: N is called an offered-arrival process on p. 8 but units sold on p. 9 and Eq. (6) → market share counts accepted sales D, separately from potential arrivals A and willing arrivals B; reason: with C=μ=Λ=c=1 and uniform demand at rate 1 the offered rate is 1 and sales rate is 1/2; units sold and Eq. (6) select D
--   - encoding: Poisson customers and independent exponential service times with non-anticipating pricing → independent marked exponential clocks, observable event histories, and independent uniform randomization; reason: uniformization generates the same loss-system law; dummy clock ticks are hidden and policies never see future marks
--   - encoding: a rate-zero no-purchase action, possibly at an infinite limiting price → an explicit no-offer action with zero transaction reward and an ignored dummy price at zero; reason: all positive-rate inverse prices are retained, including unbounded limits at zero
--   - encoding: expected real long-run liminf objectives → extended signed Lebesgue expectation and EReal liminf over real horizons; reason: finiteness is a separate theorem conclusion, so nonintegrable integrals or unbounded real suprema cannot silently become zero
--   - generalization: initial inventory is unspecified → every deterministic initial inventory q₀ in {0,…,C}; reason: the exponential model permits every initial free-inventory state; the source instance is included
--   - encoding: availability at an arrival in (1) → test pre-event free inventory and charge only accepted admission jumps; reason: a sale consumes a previously free unit; post-event inventory may be zero even for a valid sale, and the predictable convention agrees with (5)
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3 (11 February 2020), p. 11, Theorem 1, with standing assumptions §§2.1–2.3, pp. 7–10

import Mathlib
import Definitions.Def_ReusablePricingAudit_FullModel_ResourceModel

namespace ReusablePricingAudit.FullModel

/-- Theorem 1 at full model strength. The same admissible constant price satisfies
all three inequalities against a global non-anticipating optimizer. Signed and
zero benchmark metrics are retained; no positivity implication replaces profit. -/
theorem full_strength_static_pricing (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (πstar : PricingPolicy I) (hoptimal : GloballyOptimal I q₀ πstar) :
    ∃ l : Rate I,
      ((15 / 19 : ℝ) : EReal) * profitRate I q₀ πstar ≤
        profitRate I q₀ (staticPolicy I l) ∧
      ((15 / 19 : ℝ) : EReal) * salesRate I q₀ πstar ≤
        salesRate I q₀ (staticPolicy I l) ∧
      ((15 / 19 : ℝ) : EReal) * serviceLevel I q₀ πstar ≤
        serviceLevel I q₀ (staticPolicy I l) := by sorry

end ReusablePricingAudit.FullModel
