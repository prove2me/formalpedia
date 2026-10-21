-- Prove2me | Theorems.Thm_SRPTManyServer_Collapse_lemma_4
-- name    : SRPTManyServer.Collapse.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:16.649736+00:00
-- url     : https://prove2.me/theorems/006010b9-8811-4301-824a-846aaacad5fd
-- title:
--   Lemma 4, p. 16 — in the two-class preemptive loss queues, $\mathrm{Th}^\lambda_{L,1}/\lambda \to G(\tau)$
-- statement:
--   Assume the standing assumptions: service law $\nu_S$ with density $g$ and mean $1/\mu$, patience law $\nu_T$ with a density and mean $1/\theta$, both on $[0,\infty)$, $\rho > 1$, and the threshold $\tau$ given by (1), $\mathbb E[S\,\mathbf 1(S\le\tau)] = 1/(\rho\mu)$. For $s \ge 1$ consider the two-class preemptive priority loss queue $M/GI/s/s$ with $s$ servers and Poisson arrivals of rate $\lambda_s = \rho\mu s$, where class 1 consists of the customers with $S \le \tau$. Suppose that its class 1 throughput $\mathrm{Th}^s_{L,1}$ is the almost-sure limit of $N_{L,1}(t)/t$ as $t \to \infty$. Then
--   $$\lim_{s\to\infty}\frac{\mathrm{Th}^s_{L,1}}{\lambda_s} = G(\tau),\qquad G(\tau) = P(S \le \tau).$$
--
--   In words, in the overloaded many-server limit the loss system serves asymptotically all class 1 customers. Combined with Proposition 1, this bounds the throughput of SRPT from below.
--
--   **Formalization Note** The paper's sequence is indexed by $\lambda$, with $s_\lambda = \lambda/(\rho\mu)$; here it is indexed by $s \in \mathbb N$, with $\lambda_s = \rho\mu s$. The existence of the almost-sure limit for each $s$ is a hypothesis, standing for the paper's steady-state throughput.
-- source:
--   Dong & Ibrahim, On the SRPT scheduling discipline in many-server queues with impatient customers, arXiv:2102.05789v1, p. 16, Lemma 4

import Mathlib
import Definitions.Def_SRPTManyServer_Collapse_Model

namespace SRPTManyServer.Collapse

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Lemma 4** (p. 16). Under the standing assumptions, in the sequence of two-class preemptive
priority loss systems with `s` servers and arrival rate `λ_s = ρ µ s`, if the class 1 throughput
`Th^s_{L,1}` of system `s` is the almost-sure limit of `N_{L,1}(t)/t`, then
`Th^s_{L,1}/λ_s → G(τ) = P(S ≤ τ)` as `s → ∞`. -/
theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (νS νT : Measure ℝ) (g : ℝ → ℝ) (rho mu theta tau : ℝ)
    (hstd : Standing νS νT g rho mu theta tau)
    (E S T : ℕ → Ω → ℝ) (hmodel : IsArrivalModel P νS νT E S T)
    (thL1 : ℕ → ℝ)
    (hth : ∀ s : ℕ, 1 ≤ s → ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ => (lossNumCompleted1 s tau (arrivalStream rho mu s E S T ω) t : ℝ) / t)
        atTop (𝓝 (thL1 s))) :
    Tendsto (fun s : ℕ => thL1 s / (rho * mu * s)) atTop (𝓝 (νS (Set.Iic tau)).toReal) := by sorry

end SRPTManyServer.Collapse
