-- Prove2me | Theorems.Thm_WhittEfficiency_IS_sec_2_5_busy_poisson
-- name    : WhittEfficiency.IS.sec_2_5_busy_poisson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:24.79117+00:00
-- url     : https://prove2.me/theorems/22821687-7706-4237-9076-e161e656d725
-- title:
--   §2.5, p. 713 (the M/G/∞ claim) — service times dᵢ w.p. pᵢ with mean 1: N(t) ~ Poisson(λ) for t > max dᵢ
-- statement:
--   Consider an infinite-server model with Poisson arrivals of rate $\lambda > 0$, started empty at time $0$, in which the service times are i.i.d., independent of the arrival process, and take the value $d_i \ge 0$ with probability $p_i$, $i = 1, \dots, m$, where the mean service time is
--   $$\sum_{i=1}^m p_i d_i = 1.$$
--   Let $N(t)$ be the number of busy servers at time $t$. Then for every $t > \max\{d_i : 1 \le i \le m\}$, $N(t)$ has a Poisson distribution with mean $\lambda$:
--
--   $$P\big(N(t) = k\big) = e^{-\lambda}\,\frac{\lambda^k}{k!}, \qquad k = 0, 1, 2, \dots$$
--
--   In particular the (steady-state) number of busy servers depends on the service-time distribution only through its mean, so the M/D/∞ analysis behind the square-root staffing formula $s = \lambda + \gamma\sqrt\lambda$ extends to general finite service-time distributions.
--
--   **Formalization Note** The service-time law is encoded by i.i.d. class labels $J_k$ with $P(J_k = i) = p_i$, independent of the exponential interarrival times; customer $k$ has service time $d_{J_k}$. The paper's index range $1 \le i \le n$ is `Fin m`. The constraint $\sum_i p_i d_i = 1$ forces $m \ge 1$; the label law together with a probability measure forces $p_i \ge 0$ and $\sum_i p_i = 1$, so these are not separate hypotheses. "Steady state" is the law at each fixed $t > \max_i d_i$, not a limit $t \to \infty$.
-- source:
--   Whitt, Understanding the efficiency of multi-server service systems, Management Sci. 38 (1992), p. 713, §2.5, first paragraph

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

namespace WhittEfficiency.IS

/-- Whitt 1992, §2.5, p. 713 (the M/G/∞ claim): with Poisson arrivals of rate `lam` and i.i.d.
service times independent of the arrivals, taking the value `d i` with probability `p i`, where
`∑ p i * d i = 1` (mean service time `1`), the number of busy servers `N(t)` is Poisson with mean
`lam` for every `t > max d i`. -/
theorem sec_2_5_busy_poisson {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    {m : ℕ} (p d : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i) (J : ℕ → Ω → Fin m)
    (hM : IsMarkedPoisson μ lam T p J)
    (hmean : ∑ i, p i * d i = 1) (t : ℝ) (ht : ∀ i, d i < t) :
    ∀ k : ℕ, μ.real {ω | busyCount T (fun j ω => d (J j ω)) t ω = k} =
      Real.exp (-lam) * lam ^ k / k.factorial := by sorry

end WhittEfficiency.IS
