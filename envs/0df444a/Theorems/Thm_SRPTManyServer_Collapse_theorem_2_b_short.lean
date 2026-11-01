-- Prove2me | Theorems.Thm_SRPTManyServer_Collapse_theorem_2_b_short
-- name    : SRPTManyServer.Collapse.theorem_2_b_short
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T20:19:43.663211+00:00
-- url     : https://prove2.me/theorems/8bda4bec-bf05-4d86-9c43-079b69a545f1
-- title:
--   Theorem 2(b), p. 10 — under SRPT, $\mathbb E[W^\lambda_c \mid S_c\le\tau]\to 0$: short jobs wait a vanishing time
-- statement:
--   Assume the standing assumptions: service law $\nu_S$ with density $g$ and mean $1/\mu$, patience law $\nu_T$ with a density and mean $1/\theta$, both on $[0,\infty)$, $\rho > 1$, and the threshold $\tau$ given by (1), $\mathbb E[S\,\mathbf 1(S\le\tau)] = 1/(\rho\mu)$. For each $s \ge 1$, system $s$ is the $M/GI/s+GI$ queue with $s$ servers and Poisson arrivals of rate $\lambda_s = \rho\mu s$, operated on every admissible sample path by an SRPT schedule, with abandonment when a customer's cumulative time in queue reaches her patience time. Let $W^s_c$ be the waiting time of a tagged customer $c$ in steady state (the total time she spends in the system but not in service), and let
--   $$p_1(s) = P(\mathrm{Serv}^s_c \mid S_c \le \tau),\qquad p_2(s) = P(\mathrm{Serv}^s_c \mid S_c > \tau),\qquad w_1(s) = \mathbb E[W^s_c \mid S_c \le \tau].$$
--   Then the short jobs, those with $S \le \tau$, wait a vanishing amount of time on average:
--   $$\lim_{s\to\infty} w_1(s) = \lim_{s\to\infty}\mathbb E[W^s_c \mid S_c \le \tau] = 0.$$
--
--   This is the second equality of Theorem 2(b) of the source. Together with Theorem 2(a) it yields the remaining limits of Theorem 2 ($\mathbb E[W\mid\mathrm{Serv}]\to0$, $\mathbb E[W\mid\mathrm{Ab}]\to1/\theta$, $\mathbb E[W\mid S>\tau]\to1/\theta$ and $\mathbb E[W]\to(1-G(\tau))/\theta$) by sample-path bookkeeping and the strong law of large numbers.
--
--   **Formalization Note** The steady-state quantities are read as almost-sure customer long-run averages, exactly as in the formalization of Theorem 2: $w_1(s)$ is the almost-sure limit, as $N\to\infty$, of the average waiting time of the customers among $0,\dots,N-1$ with $S_n\le\tau$, and $p_1(s)$, $p_2(s)$ are the corresponding fractions of served customers. Their existence for each $s\ge1$ is assumed, standing for the paper's steady-state assumption; $p_1$ and $p_2$ are included because the source derives part (b) from part (a). The schedule hypothesis is required only on admissible paths, which carry probability one. The sequence is indexed by $s\in\mathbb N$ in place of $\lambda$.
-- source:
--   Dong & Ibrahim, On the SRPT scheduling discipline in many-server queues with impatient customers, arXiv:2102.05789v1, p. 10, Theorem 2(b) (second equality); proof in Appendix A.2, p. 18

import Mathlib
import Definitions.Def_SRPTManyServer_Collapse_Model

namespace SRPTManyServer.Collapse

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Theorem 2 (b), second limit** (p. 10). Under the standing assumptions (`ρ > 1`, `τ` as in
(1)), let system `s` (`s ≥ 1` servers, arrival rate `λ_s = ρ µ s`) be operated by an SRPT schedule
`δ s ω` on every admissible sample path. Read `P(Serv | S ≤ τ)`, `P(Serv | S > τ)` and
`E[W | S ≤ τ]` in system `s` as the almost-sure customer long-run averages `pServ1 s`, `pServ2 s`
and `w1 s`. Then the mean waiting time of short jobs vanishes: `w1 s → 0` as `s → ∞`. -/
theorem theorem_2_b_short {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (νS νT : Measure ℝ) (g : ℝ → ℝ) (rho mu theta tau : ℝ)
    (hstd : Standing νS νT g rho mu theta tau)
    (E S T : ℕ → Ω → ℝ) (hmodel : IsArrivalModel P νS νT E S T)
    (δ : ℕ → Ω → ℕ → ℝ → ℝ)
    (hδ : ∀ s : ℕ, 1 ≤ s → ∀ ω, (arrivalStream rho mu s E S T ω).Admissible →
      IsSRPTSchedule s (arrivalStream rho mu s E S T ω) (δ s ω))
    (pServ1 pServ2 w1 : ℕ → ℝ)
    (h_pServ1 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => S n ω ≤ tau)
      (fun n ω => servedInd (arrivalStream rho mu s E S T ω) (δ s ω) n) (pServ1 s))
    (h_pServ2 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => tau < S n ω)
      (fun n ω => servedInd (arrivalStream rho mu s E S T ω) (δ s ω) n) (pServ2 s))
    (h_w1 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => S n ω ≤ tau)
      (fun n ω => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n) (w1 s)) :
    Tendsto w1 atTop (𝓝 0) := by sorry

end SRPTManyServer.Collapse
