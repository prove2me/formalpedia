-- Prove2me | Theorems.Thm_SRPTManyServer_Collapse_theorem_2
-- name    : SRPTManyServer.Collapse.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:04:09.623325+00:00
-- url     : https://prove2.me/theorems/ec4d32be-cc1e-487f-b82c-30a0f700e868
-- title:
--   Theorem 2, p. 10 — under SRPT with ρ > 1, as s → ∞ class S ≤ τ is served with vanishing wait and class S > τ abandons after mean wait 1/θ
-- statement:
--   Assume the standing assumptions of the model: service times i.i.d. with law $\nu_S$, density $g$, cdf $G$ and mean $1/\mu$; patience times i.i.d. with law $\nu_T$, a density and mean $1/\theta$, both laws on $[0,\infty)$; traffic intensity $\rho > 1$; and the threshold $\tau$ defined by (1),
--   $$\lambda\,\mathbb E[S\,\mathbf 1(S\le\tau)] = s_\lambda,\qquad\text{i.e.}\qquad \mathbb E[S\,\mathbf 1(S \le \tau)] = \frac{1}{\rho\mu}.$$
--   For $s \ge 1$, system $s$ is the $M/GI/s+GI$ queue with $s$ servers and Poisson arrivals of rate $\lambda_s = \rho\mu s$, so $\rho = \lambda_s/(s\mu)$ is held fixed. It is operated under SRPT, with abandonment when the cumulative time in queue reaches the patience time. For a tagged customer $c$ in steady state, $\mathrm{Serv}_c$ denotes the event that she is served, $\mathrm{Ab}_c$ the event that she abandons, and $W_c$ her waiting time. Then, as $s \to \infty$:
--
--   1. (a) $P(\mathrm{Serv}^s_c \mid S_c \le \tau) \to 1$ and $P(\mathrm{Serv}^s_c \mid S_c > \tau) \to 0$;
--   2. (b) $\mathbb E[W^s_c \mid \mathrm{Serv}_c] \to 0$ and $\mathbb E[W^s_c \mid S_c \le \tau] \to 0$;
--   3. (c) $\mathbb E[W^s_c \mid \mathrm{Ab}_c] \to 1/\theta$ and $\mathbb E[W^s_c \mid S_c > \tau] \to 1/\theta$;
--   4. (d) $$\mathbb E[W^s_c] \to \frac{1 - G(\tau)}{\theta}.$$
--
--   Short jobs, those with $S \le \tau$, are served with vanishing delay; long jobs abandon after waiting, on average, their full mean patience. The limits depend on the patience law only through its mean.
--
--   **Formalization Note** Each steady-state tagged-customer quantity is read as an almost-sure customer long-run average in system $s$. For example, $\mathbb E[W^s_c \mid S_c \le \tau]$ is the almost-sure limit, as $N \to \infty$, of the average waiting time of the customers among $0,\dots,N-1$ with $S_n \le \tau$. The seven limits are given as functions of $s$, and their existence for each $s \ge 1$ is a hypothesis, standing for the paper's assumption of a steady state. The schedule is an arbitrary SRPT schedule, with arbitrary tie-breaking, on every admissible path; non-admissible paths have probability zero and are unconstrained. $G(\tau) = \nu_S((-\infty,\tau])$. The sequence is indexed by $s \in \mathbb N$ instead of $\lambda$, with $\lambda_s = \rho\mu s$.
-- source:
--   Dong & Ibrahim, On the SRPT scheduling discipline in many-server queues with impatient customers, arXiv:2102.05789v1, p. 10, Theorem 2

import Mathlib
import Definitions.Def_SRPTManyServer_Collapse_Model

namespace SRPTManyServer.Collapse

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Theorem 2** (p. 10), parts (a)–(d). Under the standing assumptions (`ρ > 1`, `τ` as in (1)),
let system `s` (`s ≥ 1` servers, arrival rate `λ_s = ρ µ s`) be operated by an SRPT schedule
`δ s ω` on every admissible sample path. Read the steady-state tagged-customer quantities as the
almost-sure customer long-run averages `pServ1 s = P(Serv | S ≤ τ)`, `pServ2 s = P(Serv | S > τ)`,
`wServ s = E[W | Serv]`, `w1 s = E[W | S ≤ τ]`, `wAb s = E[W | Ab]`, `w2 s = E[W | S > τ]`,
`wAll s = E[W]`. Then, as `s → ∞`,
(a) `pServ1 → 1`, `pServ2 → 0`; (b) `wServ → 0`, `w1 → 0`; (c) `wAb → 1/θ`, `w2 → 1/θ`;
(d) `wAll → (1 − G(τ))/θ`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (νS νT : Measure ℝ) (g : ℝ → ℝ) (rho mu theta tau : ℝ)
    (hstd : Standing νS νT g rho mu theta tau)
    (E S T : ℕ → Ω → ℝ) (hmodel : IsArrivalModel P νS νT E S T)
    (δ : ℕ → Ω → ℕ → ℝ → ℝ)
    (hδ : ∀ s : ℕ, 1 ≤ s → ∀ ω, (arrivalStream rho mu s E S T ω).Admissible →
      IsSRPTSchedule s (arrivalStream rho mu s E S T ω) (δ s ω))
    (pServ1 pServ2 wServ w1 wAb w2 wAll : ℕ → ℝ)
    (h_pServ1 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => S n ω ≤ tau)
      (fun n ω => servedInd (arrivalStream rho mu s E S T ω) (δ s ω) n) (pServ1 s))
    (h_pServ2 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => tau < S n ω)
      (fun n ω => servedInd (arrivalStream rho mu s E S T ω) (δ s ω) n) (pServ2 s))
    (h_wServ : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P
      (fun n ω => Completes (arrivalStream rho mu s E S T ω) (δ s ω) n)
      (fun n ω => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n) (wServ s))
    (h_w1 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => S n ω ≤ tau)
      (fun n ω => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n) (w1 s))
    (h_wAb : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P
      (fun n ω => ¬ Completes (arrivalStream rho mu s E S T ω) (δ s ω) n)
      (fun n ω => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n) (wAb s))
    (h_w2 : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun n ω => tau < S n ω)
      (fun n ω => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n) (w2 s))
    (h_wAll : ∀ s : ℕ, 1 ≤ s → HasLongRunAvg P (fun _ _ => True)
      (fun n ω => waitingTime (arrivalStream rho mu s E S T ω) (δ s ω) n) (wAll s)) :
    Tendsto pServ1 atTop (𝓝 1) ∧ Tendsto pServ2 atTop (𝓝 0) ∧
    Tendsto wServ atTop (𝓝 0) ∧ Tendsto w1 atTop (𝓝 0) ∧
    Tendsto wAb atTop (𝓝 (1 / theta)) ∧ Tendsto w2 atTop (𝓝 (1 / theta)) ∧
    Tendsto wAll atTop (𝓝 ((1 - (νS (Set.Iic tau)).toReal) / theta)) := by sorry

end SRPTManyServer.Collapse
