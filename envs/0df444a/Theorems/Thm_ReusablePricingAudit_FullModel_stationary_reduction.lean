-- Prove2me | Theorems.Thm_ReusablePricingAudit_FullModel_stationary_reduction
-- name    : ReusablePricingAudit.FullModel.stationary_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:49:52.426992+00:00
-- url     : https://prove2.me/theorems/4dfa1d32-749f-4454-92f7-73668de55d04
-- title:
--   Section 2.3 — physical stationary formulas and benchmark reduction
-- statement:
--   For every resource instance and initial free inventory $q_0$, its real inverse-demand representative with a dummy value at rate zero satisfies the published stationary standing assumptions. For every stationary feasible rate vector $\lambda=(\lambda_1,\ldots,\lambda_C)$, the physical state probabilities converge, from that initial state, to
--   $$P_i(\lambda)=\frac{\frac{C!}{(C-i)!}\prod_{j=i+1}^{C}\lambda_j/\mu}{\sum_{k=0}^{C}\frac{C!}{(C-k)!}\prod_{j=k+1}^{C}\lambda_j/\mu},\qquad 0\le i\le C.$$
--   Its physical long-run metrics equal
--   $$\mathcal P^\lambda=\sum_{i=1}^{C}\lambda_i(p(\lambda_i)-c)P_i,\quad
--   \mathcal{MS}^\lambda=\sum_{i=1}^{C}\lambda_iP_i,\quad
--   \mathcal{SL}^\lambda=\sum_{i=1}^{C}P_i,$$
--   where every zero-rate reward term is zero. This includes reducible chains caused by zero rates.
--
--   Writing $\Pi_{\mathrm{stat}}$ for stationary policies in the physical policy class, the benchmark satisfies
--   $$\sup_{\pi\in\Pi}W(\pi)=\sup_{\lambda\in\Pi_{\mathrm{stat}}}W(\lambda).$$
--   Moreover, for every $\pi\in\Pi$ and $\varepsilon>0$ there is one stationary vector $\lambda$ with each of its three metrics at least the corresponding metric of $\pi$ minus $\varepsilon$.
--
--   The conclusion connects the source's physical model to the reused stationary algebra. The coordinate clause is an additional open proof obligation; it is not inferred from weighted-value equality and it does not assert an exact stationary representative for every optimizer.
--
--   Differences from the source:
--   - encoding: Poisson customers and independent exponential service times with non-anticipating pricing → independent marked exponential clocks, observable event histories, and independent uniform randomization; reason: uniformization generates the same loss-system law; dummy clock ticks are hidden and policies never see future marks
--   - encoding: a rate-zero no-purchase action, possibly at an infinite limiting price → an explicit no-offer action with zero transaction reward and an ignored dummy price at zero; reason: all positive-rate inverse prices are retained, including unbounded limits at zero
--   - encoding: expected real long-run liminf objectives → extended signed Lebesgue expectation and EReal liminf over real horizons; reason: finiteness is a separate theorem conclusion, so nonintegrable integrals or unbounded real suprema cannot silently become zero
--   - reading: N is called an offered-arrival process on p. 8 but units sold on p. 9 and Eq. (6) → market share counts accepted sales D, separately from potential arrivals A and willing arrivals B; reason: with C=μ=Λ=c=1 and uniform demand at rate 1 the offered rate is 1 and sales rate is 1/2; units sold and Eq. (6) select D
--   - generalization: initial inventory is unspecified → every deterministic initial inventory q₀ in {0,…,C}; reason: the exponential model permits every initial free-inventory state; the source instance is included
--   - reading: without loss of optimality one may focus on stationary policies → equality of physical and stationary suprema, without an assertion of maximum attainment; reason: the source denotes chosen optimizers but gives no endpoint attainment theorem; equality of optimal values preserves the benchmark without inventing existence
--   - generalization: stationary policies suffice for the weighted benchmark → also approximate every admissible policy coordinatewise within every positive ε by a stationary policy; reason: scalar optimal-value equality alone cannot justify comparisons of the three coordinates; the stronger vector statement includes that reduction
--   - encoding: availability at an arrival in (1) → test pre-event free inventory and charge only accepted admission jumps; reason: a sale consumes a previously free unit; post-event inventory may be zero even for a valid sale, and the predictable convention agrees with (5)
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3 (11 February 2020), p. 10, §2.3 opening stationary-reduction paragraph, stationary-distribution display and (5)–(7)

import Mathlib
import Definitions.Def_ReusablePricingAudit_FullModel_ResourceModel
import Definitions.Def_StaticReusable_Guarantee_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace ReusablePricingAudit.FullModel

/-- §2.3, p. 10: the physical benchmark equals the stationary supremum, and
the stationary formulas are the actual limits, including zero rates. The
coordinate approximation supplies a vector bridge, not merely scalar equality.
Suprema are not asserted to be attained at discontinuous endpoint prices. -/
theorem stationary_reduction (I : ResourceInstance) (q₀ : Fin (I.C + 1)) :
    StaticReusable.Guarantee.Standing I.C I.μ I.Λ I.c (auxiliaryPrice I) I.α₁ I.α₂ I.α₃ ∧
    (∀ lam : StationaryRates I,
      (∀ i : Fin (I.C + 1),
        Tendsto (fun t : ℝ =>
          ((∫⁻ ω, if freeUnits I q₀ (stationaryPolicy I lam) ω t = i.val then 1 else 0
            ∂resourceLaw I) : EReal)) atTop
          (nhds ((StaticReusable.Guarantee.prob I.C I.μ (fun j => (lam j).val) i.val : ℝ) : EReal))) ∧
      profitRate I q₀ (stationaryPolicy I lam) =
        ((StaticReusable.Guarantee.profit I.C I.μ (auxiliaryPrice I) I.c
          (fun j => (lam j).val) : ℝ) : EReal) ∧
      salesRate I q₀ (stationaryPolicy I lam) =
        ((StaticReusable.Guarantee.marketShare I.C I.μ (fun j => (lam j).val) : ℝ) : EReal) ∧
      serviceLevel I q₀ (stationaryPolicy I lam) =
        ((StaticReusable.Guarantee.serviceLevel I.C I.μ (fun j => (lam j).val) : ℝ) : EReal)) ∧
    benchmark I q₀ = ⨆ lam : StationaryRates I, weightedValue I q₀ (stationaryPolicy I lam) ∧
    (∀ π : PricingPolicy I, ∀ ε : ℝ, 0 < ε → ∃ lam : StationaryRates I,
      profitRate I q₀ π - (ε : EReal) ≤ profitRate I q₀ (stationaryPolicy I lam) ∧
      salesRate I q₀ π - (ε : EReal) ≤ salesRate I q₀ (stationaryPolicy I lam) ∧
      serviceLevel I q₀ π - (ε : EReal) ≤ serviceLevel I q₀ (stationaryPolicy I lam)) := by sorry

end ReusablePricingAudit.FullModel
