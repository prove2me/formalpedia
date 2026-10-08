-- Prove2me | Theorems.Thm_ServiceParts_Shortfall_discrete_stationary_distribution
-- name    : ServiceParts.Shortfall.discrete_stationary_distribution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T23:41:17.212988+00:00
-- url     : https://prove2.me/theorems/dfc842a8-4eb4-4bd5-9672-f8d48a3ac2ba
-- title:
--   Section 8.1.2 — for E[D] < c the steady-state law π = lim P{Vₙ = i} exists and solves π𝒫 = π, Σπᵢ = 1, πᵢ ≥ 0
-- statement:
--   In the discrete-demand shortfall model with $E[D] < c$, let $V_n$ be the shortfall chain started from $V_0 = 0$ and let $\mathcal P = [p_{ij}]$ be its transition matrix. Then the limits
--   $$\pi_i = \lim_{n \to \infty} P\{V_n = i\}, \qquad i = 0, 1, 2, \dots$$
--   exist, and $\pi$ solves
--   $$\pi \mathcal P = \pi, \qquad \sum_i \pi_i = 1, \qquad \pi_i \ge 0,$$
--   that is, $\sum_i \pi_i p_{ij} = \pi_j$ for every state $j$.
--
--   This is the steady-state distribution of the shortfall in the discrete case, from which Table 8.1 and Figures 8.3–8.8 are computed.
--
--   **Formalization Note** The book writes "a steady state distribution exists ... Let the stationary distribution that $V = i$ be denoted by $\pi_i$"; the statement pins $\pi_i$ to the limit of $P\{V_n = i\}$ from $V_0 = 0$. The series are stated with `HasSum`, so convergence is part of the claim.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 186, Section 8.1.2 (stationary equations)

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_DiscreteShortfallModel

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Shortfall

/-- Section 8.1.2, p. 186. Since `E[D] < c`, the shortfall chain started from `V_0 = 0` has a
steady-state distribution `π_i = lim_{n → ∞} P{V_n = i}`, and `π` solves
`π𝒫 = π`, `∑ π_i = 1`, `π_i ≥ 0`, where `𝒫 = [p_{ij}]` is the transition matrix of p. 185. -/
theorem discrete_stationary_distribution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : DiscreteShortfallModel Ω P) :
    ∃ π : ℕ → ℝ,
      (∀ i, Tendsto (fun n : ℕ => (P {ω | M.shortfall n ω = i}).toReal) atTop (𝓝 (π i))) ∧
      (∀ j, HasSum (fun i => π i * M.transProb i j) (π j)) ∧
      HasSum π 1 ∧
      (∀ i, 0 ≤ π i) := by sorry

end ServiceParts.Shortfall
