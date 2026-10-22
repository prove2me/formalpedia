-- Prove2me | Theorems.Thm_RiskPostpone_Threshold_property_2
-- name    : RiskPostpone.Threshold.property_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:46:45.608981+00:00
-- url     : https://prove2.me/theorems/e2322d8a-392d-4049-bcb5-1e3264f24d15
-- title:
--   Property 2 — the CVaR of a profit concave in q is concave in q
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\eta\in(0,1]$, $S\subseteq\mathbb R$ a convex set of decisions, and $\pi(q\mid\omega)$ a random profit such that $q\mapsto\pi(q\mid\omega)$ is concave on $S$ for every outcome $\omega$ and $\pi(q\mid\cdot)$ is integrable for every $q\in S$. Then
--   $$
--   q\ \longmapsto\ \mathrm{CVaR}_\eta(\pi(q))=\max_{v\in\mathbb R}\Big\{v+\frac1\eta\mathbb E\min\{\pi(q)-v,0\}\Big\}
--   $$
--   is concave on $S$.
--
--   The paper uses this property to obtain concavity of the responsive objective $\Pi_r(q_r)$.
--
--   **Formalization Note** The concave domain is an arbitrary convex subset of $\mathbb R$; integrability guarantees that the supremum over $v$ is finite.
-- source:
--   Kouvelis, Xiao and Yang, Role of Risk Aversion in Price Postponement under Supply Random Yield, accepted manuscript MS-OPM-18-01273.R2 (Management Science 67(8), 2021, doi:10.1287/mnsc.2020.3755), p. ec15 (PDF 48), Property 2

import Mathlib
import Definitions.Def_RiskPostpone_Threshold_CVaR

open MeasureTheory Set

namespace RiskPostpone.Threshold

/-- Property 2 (p. ec15): if the random profit `π(q | ω)` is concave in the decision `q` on a
convex set `S` for every outcome `ω`, and integrable for every `q ∈ S`, then for `η ∈ (0,1]`
`q ↦ CVaR_η(π(q)) = max_v { v + (1/η) E[min{π(q) − v, 0}] }` is concave on `S`. -/
theorem property_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : η ∈ Ioc (0 : ℝ) 1) (S : Set ℝ) (hS : Convex ℝ S) (π : ℝ → Ω → ℝ)
    (hconc : ∀ ω, ConcaveOn ℝ S (fun q => π q ω))
    (hint : ∀ q ∈ S, Integrable (π q) μ) :
    ConcaveOn ℝ S (fun q => cvar μ η (π q)) := by sorry

end RiskPostpone.Threshold
