-- Prove2me | Theorems.Thm_SRPTManyServer_Collapse_theorem_2_a
-- name    : SRPTManyServer.Collapse.theorem_2_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:36.869215+00:00
-- url     : https://prove2.me/theorems/a4fee09b-ef17-4b83-9a7b-da05607b4a3b
-- title:
--   Theorem 2(a), p. 10 — under SRPT, $P(\mathrm{Serv}^\lambda_c \mid S_c\le\tau)\to 1$ and $P(\mathrm{Serv}^\lambda_c \mid S_c>\tau)\to 0$
-- statement:
--   Assume the standing assumptions: service law $\nu_S$ with density $g$ and mean $1/\mu$, patience law $\nu_T$ with a density and mean $1/\theta$, both on $[0,\infty)$, $\rho > 1$, and the threshold $\tau$ given by (1). For each $s \ge 1$, system $s$ is the $M/GI/s+GI$ queue with $s$ servers and Poisson arrivals of rate $\lambda_s = \rho\mu s$, operated on every admissible sample path by an SRPT schedule. Let
--   $$p_1(s) = P(\mathrm{Serv}^s_c \mid S_c \le \tau),\qquad p_2(s) = P(\mathrm{Serv}^s_c \mid S_c > \tau)$$
--   be the steady-state probabilities that a tagged customer is served, given that her service time is at most $\tau$ or exceeds $\tau$. Then
--   $$\lim_{s\to\infty} p_1(s) = 1,\qquad \lim_{s\to\infty} p_2(s) = 0.$$
--
--   This is the state-space collapse: in the overloaded many-server limit SRPT behaves like a two-class priority system that serves every job shorter than $\tau$ and none longer.
--
--   **Formalization Note** The steady-state conditional probabilities are read as almost-sure customer long-run averages: $p_1(s)$ is the almost-sure limit, as $N\to\infty$, of the fraction of served customers among customers $0,\dots,N-1$ with $S_n \le \tau$, and similarly for $p_2(s)$. Their existence for each $s$ is assumed, as the paper assumes the steady state. The schedule hypothesis is required only on admissible paths, which carry probability one. The sequence is indexed by $s \in \mathbb N$ in place of $\lambda$.
-- source:
--   Dong & Ibrahim, On the SRPT scheduling discipline in many-server queues with impatient customers, arXiv:2102.05789v1, p. 10, Theorem 2(a)

import Mathlib
import Definitions.Def_SRPTManyServer_Collapse_Model

namespace SRPTManyServer.Collapse

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Theorem 2 (a)** (p. 10). Under the standing assumptions (`ρ > 1`, `τ` as in (1)), let system
`s` (`s ≥ 1` servers, arrival rate `λ_s = ρ µ s`) be operated by an SRPT schedule `δ s ω` on every
admissible sample path, and read `P(Serv | S ≤ τ)` and `P(Serv | S > τ)` in system `s` as the
almost-sure customer long-run fractions `pServ1 s` and `pServ2 s` of served customers among those
with `S ≤ τ` and with `S > τ`. Then `pServ1 s → 1` and `pServ2 s → 0` as `s → ∞`. -/
theorem theorem_2_a {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (νS νT : Measure ℝ) (g : ℝ → ℝ) (rho mu theta tau : ℝ)
    (hstd : Standing νS νT g rho mu theta tau)
    (E S T : ℕ → Ω → ℝ) (hmodel : IsArrivalModel P νS νT E S T)
    (δ : ℕ → Ω → ℕ → ℝ → ℝ)
    (hδ : ∀ s : ℕ, 1 ≤ s → ∀ ω, (arrivalStream rho mu s E S T ω).Admissible →
      IsSRPTSchedule s (arrivalStream rho mu s E S T ω) (δ s ω))
    (pServ1 pServ2 : ℕ → ℝ)
    (h_pServ1 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => S n ω ≤ tau)
      (fun n ω => servedInd (arrivalStream rho mu s E S T ω) (δ s ω) n) (pServ1 s))
    (h_pServ2 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => tau < S n ω)
      (fun n ω => servedInd (arrivalStream rho mu s E S T ω) (δ s ω) n) (pServ2 s)) :
    Tendsto pServ1 atTop (𝓝 1) ∧ Tendsto pServ2 atTop (𝓝 0) := by sorry

end SRPTManyServer.Collapse
