-- Prove2me | Theorems.Thm_ReusablePricingAudit_FullModel_physical_compatibility
-- name    : ReusablePricingAudit.FullModel.physical_compatibility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:49:15.979594+00:00
-- url     : https://prove2.me/theorems/6f0ec3e3-e9d6-48f5-870a-3cc83de25214
-- title:
--   Sections 2.1–2.3 — physical reward and counting-process compatibility
-- statement:
--   Fix any resource instance, initial free inventory $q_0$, and admissible observable-history policy $\pi$. The constructed primitive law is a probability law, its clock events tend to infinity almost surely, and $Q^\pi(t)\le C$ for every time almost surely. There is a finite instance-dependent bound $B\ge0$ such that $|r(l)|\le B$ for every $l\in[0,\Lambda]$.
--
--   Let $G_T$ be the actual total accepted-sales margin up to $T$, and let $l(t)$ and $Q(t-)$ be the predictable rate and pre-event inventory. For every $T\ge0$, both $G_T$ and the integrated net-rate reward are integrable, and
--   $$\mathbb E[G_T]=\mathbb E\!\left[\int_0^T1_{\{Q(t-)>0\}}r(l(t))\,dt\right],$$
--   $$\mathbb E[D^\pi(T)]=\mathbb E\!\left[\int_0^T1_{\{Q(t-)>0\}}l(t)\,dt\right],\qquad \mathbb E[A(T)]=\Lambda T.$$
--   Finally the three long-run metrics are finite real numbers $b,m,s$, with $0\le m\le\Lambda$ and $0\le s\le1$.
--
--   This supplies the physical reward identification and finiteness obligations for the source's expected long-run definitions. These are open theorem conclusions, not assumptions restricting the policy class. The finite bound $B$ is a bound for this instance's net-rate function, not a replacement for the universal approximation constant.
--
--   Differences from the source:
--   - encoding: Poisson customers and independent exponential service times with non-anticipating pricing → independent marked exponential clocks, observable event histories, and independent uniform randomization; reason: uniformization generates the same loss-system law; dummy clock ticks are hidden and policies never see future marks
--   - encoding: a rate-zero no-purchase action, possibly at an infinite limiting price → an explicit no-offer action with zero transaction reward and an ignored dummy price at zero; reason: all positive-rate inverse prices are retained, including unbounded limits at zero
--   - encoding: expected real long-run liminf objectives → extended signed Lebesgue expectation and EReal liminf over real horizons; reason: finiteness is a separate theorem conclusion, so nonintegrable integrals or unbounded real suprema cannot silently become zero
--   - reading: N is called an offered-arrival process on p. 8 but units sold on p. 9 and Eq. (6) → market share counts accepted sales D, separately from potential arrivals A and willing arrivals B; reason: with C=μ=Λ=c=1 and uniform demand at rate 1 the offered rate is 1 and sales rate is 1/2; units sold and Eq. (6) select D
--   - generalization: initial inventory is unspecified → every deterministic initial inventory q₀ in {0,…,C}; reason: the exponential model permits every initial free-inventory state; the source instance is included
--   - encoding: availability at an arrival in (1) → test pre-event free inventory and charge only accepted admission jumps; reason: a sale consumes a previously free unit; post-event inventory may be zero even for a valid sale, and the predictable convention agrees with (5)
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3 (11 February 2020), pp. 7–10, §§2.1–2.3, (1), market-share/service displays, and (5)–(7)

import Mathlib
import Definitions.Def_ReusablePricingAudit_FullModel_ResourceModel

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace ReusablePricingAudit.FullModel

/-- §§2.1–2.3: the primitive construction is a nonexplosive physical loss process.
Its accepted-sales and signed-profit compensators give the expected physical
objectives. All finiteness facts are conclusions, never model assumptions. -/
theorem physical_compatibility (I : ResourceInstance) (q₀ : Fin (I.C + 1))
    (π : PricingPolicy I) :
    IsProbabilityMeasure (resourceLaw I) ∧
    (∀ᵐ ω ∂resourceLaw I,
      Tendsto (eventTime ω.2) atTop atTop ∧
      ∀ t : ℝ, freeUnits I q₀ π ω t ≤ I.C) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ l ∈ Set.Icc 0 I.Λ, |netRate I l| ≤ B) ∧
    (∀ T : ℝ, 0 ≤ T →
      Integrable (fun ω => transactionProfit I q₀ π ω T) (resourceLaw I) ∧
      Integrable (fun ω => ∫ t in Set.Ioc 0 T,
        if 0 < (preDecision I q₀ π ω t).1 then
          netRate I (preDecision I q₀ π ω t).2 else 0) (resourceLaw I) ∧
      signedExpectation (resourceLaw I) (fun ω => transactionProfit I q₀ π ω T) =
        (((∫ ω, (∫ t in Set.Ioc 0 T,
          if 0 < (preDecision I q₀ π ω t).1 then
            netRate I (preDecision I q₀ π ω t).2 else 0) ∂resourceLaw I) : ℝ) : EReal) ∧
      (∫⁻ ω, (acceptedSales I q₀ π ω T : ℝ≥0∞) ∂resourceLaw I) =
        ∫⁻ ω, (∫⁻ t in Set.Ioc 0 T,
          if 0 < (preDecision I q₀ π ω t).1 then
            ENNReal.ofReal (preDecision I q₀ π ω t).2 else 0) ∂resourceLaw I ∧
      (∫⁻ ω, (potentialArrivals I q₀ π ω T : ℝ≥0∞) ∂resourceLaw I) =
        ENNReal.ofReal (I.Λ * T)) ∧
    (∃ b m s : ℝ, profitRate I q₀ π = (b : EReal) ∧
      salesRate I q₀ π = (m : EReal) ∧ serviceLevel I q₀ π = (s : EReal) ∧
      0 ≤ m ∧ m ≤ I.Λ ∧ 0 ≤ s ∧ s ≤ 1) := by sorry

end ReusablePricingAudit.FullModel
