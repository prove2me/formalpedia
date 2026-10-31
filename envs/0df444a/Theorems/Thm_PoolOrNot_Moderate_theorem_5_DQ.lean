-- Prove2me | Theorems.Thm_PoolOrNot_Moderate_theorem_5_DQ
-- name    : PoolOrNot.Moderate.theorem_5_DQ
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T10:20:41.679378+00:00
-- url     : https://prove2.me/theorems/73fbb0a4-0d86-4126-b4e2-59f65f3a9b3d
-- title:
--   Theorem 5, pp. 10–11, DQ–JSQ half — moderate-overload limits of occupancy, abandonment, AWT, delay, waits and PWT variance
-- statement:
--   This is the dedicated-queue (DQ–JSQ) half of Theorem 5 of Cao, He, Huang and Liu.
--
--   Let $\mu,\theta>0$ and, for each $n\ge 1$, let $\lambda_n>0$ be the total arrival rate of the $n$-th DQ–JSQ system: $n$ servers, each with its own queue, arrivals routed by join-the-shortest-queue, exponential services of rate $\mu$ and exponential patience of rate $\theta$. Assume (21), $\lambda_n/(n\mu)\to\rho$, in moderate overload
--   $$1<\rho<1+\frac{\theta}{\mu}.$$
--   Let $\pi_n$ be any stationary law of the $n$-th chain (on the augmented queue-length space), $W^n_D$ the steady-state potential waiting time (an arrival seeing $\pi_n$ joins a server with $i$ customers and waits $T_a(i)$), $R\sim\mathrm{Exp}(\theta)$ independent of $W^n_D$, $V^n_D=W^n_D\wedge R$, and $\bar X^n_D(\infty)$ the stationary number in system divided by $n$. With $q=\mu(\rho-1)/\theta$ and $r=q-\lfloor q\rfloor$ as in (18):
--
--   0. for every $n\ge1$, the law of $W^n_D$ is a probability law with finite second moment and $E[\bar X^n_D(\infty)]$ is a convergent series;
--   1. $E[\bar X^n_D(\infty)]\to q+1$;
--   2. $P^n_D(\mathrm{Ab})=P(R<W^n_D)\to(\rho-1)/\rho$;
--   3. $E[V^n_D]\to q/(\rho\mu)$;
--   4. $P^n_D(\mathrm{De})=P(W^n_D>0)\to r(\mu+\theta)/(\rho\mu)$;
--   5. $E[W^n_D\mid W^n_D>0]\to 1/\mu$;
--   6. $E[W^n_D]\to r(\mu+\theta)/(\rho\mu^2)$;
--   7. $E[V^n_D\mid W^n_D\le R]\to r/(\mu+\theta)$;
--   8. $E[V^n_D\mid W^n_D>R]\to 1/(\mu+\theta)$;
--   9. $\displaystyle \mathrm{Var}(W^n_D)\to\frac{r(\mu+\theta)}{\rho\mu^3}\Bigl(2-\frac{r(\mu+\theta)}{\rho\mu}\Bigr)$.
--
--   These are exactly the DQ limits of Theorem 5 (i)–(ix); together with the M/M/n+M limits (Whitt 2004; Garnett et al. 2002 for (ii)) and the elementary comparisons between the two sets of limits, they give the full theorem.
--
--   **Formalization Note** Same objects as the parent `PoolOrNot.Moderate.theorem_5`: the chain generator `genAb`, the PWT law `pwtLawD` and the measures of `Def_PoolOrNot_Moderate_Waiting`. The well-posedness conjunct (item 0) is the DQ part of the parent's strengthening guard, ruling out Lean's default values for divergent series and non-integrable functions.
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research 69(6):1866-1885 (2021), doi:10.1287/opre.2019.1976, pp. 10-11 (PDF 11-12), Theorem 5

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_ErlangA_Abandonment_Model
import Definitions.Def_ErlangA_Staffing_Model
import Definitions.Def_PoolOrNot_Moderate_Chain
import Definitions.Def_PoolOrNot_Moderate_Waiting

open Filter Topology MeasureTheory ProbabilityTheory JSQHalfinWhitt.Tightness

namespace PoolOrNot.Moderate

/-- **Theorem 5**, pp. 10–11, DQ–JSQ half. -/
theorem theorem_5_DQ (μ θ ρ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n)
    (h21 : Tendsto (fun n : ℕ => lam n / ((n : ℝ) * μ)) atTop (𝓝 ρ))
    (hρ1 : 1 < ρ) (hρ2 : ρ < 1 + θ / μ)
    (π : (n : ℕ) → State n → ℝ)
    (hπ : ∀ n : ℕ, 1 ≤ n → IsStationaryDist (genAb n (lam n) μ θ) (π n)) :
    (∀ n : ℕ, 1 ≤ n →
      IsProbabilityMeasure (pwtLawD (π n) μ θ) ∧
      Integrable (fun w : ℝ => w ^ 2) (pwtLawD (π n) μ θ) ∧
      Summable (fun q : State n => π n q * ((∑' i : ℕ, (q.1 i : ℝ)) / (n : ℝ)))) ∧
    Tendsto (fun n : ℕ => meanOccD (π n)) atTop (𝓝 (qOf ρ μ θ + 1)) ∧
    Tendsto (fun n : ℕ => probAb (pwtLawD (π n) μ θ) θ) atTop (𝓝 ((ρ - 1) / ρ)) ∧
    Tendsto (fun n : ℕ => meanAWT (pwtLawD (π n) μ θ) θ) atTop (𝓝 (qOf ρ μ θ / (ρ * μ))) ∧
    Tendsto (fun n : ℕ => probDelay (pwtLawD (π n) μ θ)) atTop
        (𝓝 (rOf ρ μ θ * (μ + θ) / (ρ * μ))) ∧
    Tendsto (fun n : ℕ => meanPWTDelayed (pwtLawD (π n) μ θ)) atTop (𝓝 (1 / μ)) ∧
    Tendsto (fun n : ℕ => meanPWT (pwtLawD (π n) μ θ)) atTop
        (𝓝 (rOf ρ μ θ * (μ + θ) / (ρ * μ ^ 2))) ∧
    Tendsto (fun n : ℕ => meanAWTServed (pwtLawD (π n) μ θ) θ) atTop
        (𝓝 (rOf ρ μ θ / (μ + θ))) ∧
    Tendsto (fun n : ℕ => meanAWTAband (pwtLawD (π n) μ θ) θ) atTop (𝓝 (1 / (μ + θ))) ∧
    Tendsto (fun n : ℕ => varPWT (pwtLawD (π n) μ θ)) atTop
        (𝓝 ((rOf ρ μ θ * (μ + θ) / (ρ * μ ^ 3)) * (2 - rOf ρ μ θ * (μ + θ) / (ρ * μ)))) := by sorry

end PoolOrNot.Moderate
