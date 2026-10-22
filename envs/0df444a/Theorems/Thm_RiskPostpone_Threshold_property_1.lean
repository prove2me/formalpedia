-- Prove2me | Theorems.Thm_RiskPostpone_Threshold_property_1
-- name    : RiskPostpone.Threshold.property_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:50.059251+00:00
-- url     : https://prove2.me/theorems/555e9ece-c731-4087-aeac-6772681e202d
-- title:
--   Property 1 (corrected: continuous profit) — CVaR_η(π) = E[π | π ≤ VaR_η(π)] equals the maximization formula
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\eta\in(0,1]$, and let $\pi$ be an integrable random profit, essentially bounded above, whose distribution has no atoms. Put $v^*=\mathrm{VaR}_\eta(\pi)$. Then
--
--   1. $\mathbb P(\pi\le v^*)=\eta$;
--   2. the function $F(v)=v+\frac1\eta\mathbb E\min\{\pi-v,0\}$ attains its maximum over $v\in\mathbb R$ at $v=v^*$;
--   3. the maximization formula equals the conditional tail expectation:
--   $$
--   \max_{v\in\mathbb R}\Big\{v+\frac1\eta\mathbb E\min\{\pi-v,0\}\Big\}=\mathbb E\big[\pi\mid \pi\le \mathrm{VaR}_\eta(\pi)\big]=\frac{\mathbb E\big[\pi\,\mathbf 1\{\pi\le v^*\}\big]}{\mathbb P(\pi\le v^*)}.
--   $$
--
--   This identifies the CVaR used throughout the paper with the average profit in the lower $\eta$-tail, and shows that the VaR is an optimal $v$.
--
--   **Formalization Note** The paper states the equivalence for every random profit; it fails when the profit has an atom at its VaR (then $\mathbb P(\pi\le\mathrm{VaR})>\eta$ and the conditional expectation differs from the formula), so the statement assumes the law of $\pi$ has no atoms, as the paper's proof implicitly does. The profit is a measurable function on a general probability space; conditional expectation on the event is written as the ratio. The profit is assumed essentially bounded above (every profit in the paper is bounded): otherwise at $\eta=1$ the set $\{v:\mathbb P(\pi\le v)\ge1\}$ is empty, the paper's VaR is $+\infty$, and Lean's infimum of the empty set is the junk value $0$.
-- source:
--   Kouvelis, Xiao and Yang, Role of Risk Aversion in Price Postponement under Supply Random Yield, accepted manuscript MS-OPM-18-01273.R2 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3755), p. ec14 (PDF 47), Property 1; proof p. ec15 (PDF 48)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RiskPostpone_Threshold_CVaR

open MeasureTheory Set

namespace RiskPostpone.Threshold

/-- Property 1 (p. ec14), corrected to a continuously distributed profit: for `η ∈ (0,1]` and an
integrable random profit `X`, essentially bounded above (so that `VaR_η(X)` is a real number also
at `η = 1`), whose law has no atoms, with `v* = VaR_η(X)`,
(i) `P(X ≤ v*) = η`;
(ii) the Rockafellar–Uryasev bracket `v ↦ v + (1/η) E[min{X − v, 0}]` attains its maximum at
`v = v*`;
(iii) `CVaR_η(X) = E[X | X ≤ VaR_η(X)] = E[X·1{X ≤ v*}] / P(X ≤ v*)`. -/
theorem property_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : η ∈ Ioc (0 : ℝ) 1) (X : Ω → ℝ) (hXm : Measurable X)
    (hXi : Integrable X μ) (hXb : ∃ C : ℝ, ∀ᵐ ω ∂μ, X ω ≤ C) (hatom : NullSingletonClass (μ.map X)) :
    (μ {ω | X ω ≤ MultistageStochastic.valueAtRisk μ X η}).toReal = η ∧
    IsGreatest (range fun v : ℝ => v + (1 / η) * ∫ ω, min (X ω - v) 0 ∂μ)
      (MultistageStochastic.valueAtRisk μ X η + (1 / η) * ∫ ω, min (X ω - MultistageStochastic.valueAtRisk μ X η) 0 ∂μ) ∧
    cvar μ η X =
      (∫ ω in {ω | X ω ≤ MultistageStochastic.valueAtRisk μ X η}, X ω ∂μ) / (μ {ω | X ω ≤ MultistageStochastic.valueAtRisk μ X η}).toReal := by sorry

end RiskPostpone.Threshold
