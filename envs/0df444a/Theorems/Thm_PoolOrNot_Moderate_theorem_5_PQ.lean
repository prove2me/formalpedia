-- Prove2me | Theorems.Thm_PoolOrNot_Moderate_theorem_5_PQ
-- name    : PoolOrNot.Moderate.theorem_5_PQ
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-30T10:20:55.185984+00:00
-- url     : https://prove2.me/theorems/4fc85289-0220-42a7-a77c-062ecf37f465
-- title:
--   Theorem 5, pp. 10–11, M/M/n+M half (Whitt 2004) — efficiency-driven limits of occupancy, AWT, delay, waits and PWT variance
-- statement:
--   This is the pooled (M/M/n+M, Erlang-A) half of Theorem 5 of Cao, He, Huang and Liu, apart from part (ii) (which is Theorem 1 of Garnett, Mandelbaum and Reiman 2002). The paper attributes these limits to Whitt (2004).
--
--   Let $\mu,\theta>0$, let $\lambda_n>0$ be the arrival rate of the $n$-th M/M/n+M queue ($n$ servers of rate $\mu$, one pooled queue, exponential patience of rate $\theta$), and assume (21), $\lambda_n/(n\mu)\to\rho$ with $\rho>1$ (efficiency-driven overload). Let $\pi^{(n)}$ be its stationary law of the number in system, $W^n_P$ the steady-state potential waiting time (an arrival finding $n+m$ customers waits a sum of $m+1$ independent exponentials of rates $n\mu+j\theta$, $j=0,\dots,m$, and an arrival finding fewer than $n$ waits $0$), $R\sim\mathrm{Exp}(\theta)$ independent of $W^n_P$, $V^n_P=W^n_P\wedge R$, and $\bar X^n_P(\infty)$ the stationary number in system divided by $n$. With $q=\mu(\rho-1)/\theta$ and $w=\ln(\rho)/\theta$:
--
--   0. for every $n\ge1$, the law of $W^n_P$ is a probability law with finite second moment and $E[\bar X^n_P(\infty)]=\sum_k k\pi^{(n)}_k/n$ is a convergent series;
--   1. $E[\bar X^n_P(\infty)]\to q+1$;
--   2. $E[V^n_P]\to q/(\rho\mu)$;
--   3. $P^n_P(\mathrm{De})=P(W^n_P>0)\to 1$;
--   4. $E[W^n_P\mid W^n_P>0]\to w$;
--   5. $E[W^n_P]\to w$;
--   6. $E[V^n_P\mid W^n_P\le R]\to w$;
--   7. $\displaystyle E[V^n_P\mid W^n_P>R]\to -\frac{\mu w}{\theta q}+\frac1\theta$;
--   8. $\mathrm{Var}(W^n_P)\to 0$.
--
--   In the efficiency-driven regime the potential wait of the pooled system concentrates at the deterministic value $w=\ln(\rho)/\theta$, where the fraction $e^{-\theta w}=1/\rho$ of customers is served; these limits are the PQ column of Theorem 5 (i), (iii)–(ix).
--
--   **Formalization Note** Uses `ErlangA.Abandonment.stationaryDist`, `ErlangA.Staffing.probWait` and the PWT law `pwtLawP` of `Def_PoolOrNot_Moderate_Waiting`. The parent's upper bound $\rho<1+\theta/\mu$ is not assumed: the pooled limits hold for every $\rho>1$. Item 0 is the PQ part of the parent's strengthening guard.
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research 69(6):1866-1885 (2021), doi:10.1287/opre.2019.1976, pp. 10-11 (PDF 11-12), Theorem 5 (PQ limits attributed there to Whitt 2004, Efficiency-driven heavy-traffic approximations for many-server queues with abandonments, Management Science 50(10):1449-1461)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_ErlangA_Abandonment_Model
import Definitions.Def_ErlangA_Staffing_Model
import Definitions.Def_PoolOrNot_Moderate_Chain
import Definitions.Def_PoolOrNot_Moderate_Waiting

open Filter Topology MeasureTheory ProbabilityTheory JSQHalfinWhitt.Tightness

namespace PoolOrNot.Moderate

/-- **Theorem 5**, pp. 10–11, M/M/n+M half (Whitt 2004), except (ii). -/
theorem theorem_5_PQ (μ θ ρ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n)
    (h21 : Tendsto (fun n : ℕ => lam n / ((n : ℝ) * μ)) atTop (𝓝 ρ))
    (hρ1 : 1 < ρ) :
    (∀ n : ℕ, 1 ≤ n →
      IsProbabilityMeasure (pwtLawP n (lam n) μ θ) ∧
      Integrable (fun w : ℝ => w ^ 2) (pwtLawP n (lam n) μ θ) ∧
      Summable (fun k : ℕ => (k : ℝ) * ErlangA.Abandonment.stationaryDist n (lam n) μ θ k)) ∧
    Tendsto (fun n : ℕ => meanOccP n (lam n) μ θ) atTop (𝓝 (qOf ρ μ θ + 1)) ∧
    Tendsto (fun n : ℕ => meanAWT (pwtLawP n (lam n) μ θ) θ) atTop
        (𝓝 (qOf ρ μ θ / (ρ * μ))) ∧
    Tendsto (fun n : ℕ => ErlangA.Staffing.probWait n (lam n) μ θ) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => meanPWTDelayed (pwtLawP n (lam n) μ θ)) atTop
        (𝓝 (Real.log ρ / θ)) ∧
    Tendsto (fun n : ℕ => meanPWT (pwtLawP n (lam n) μ θ)) atTop (𝓝 (Real.log ρ / θ)) ∧
    Tendsto (fun n : ℕ => meanAWTServed (pwtLawP n (lam n) μ θ) θ) atTop
        (𝓝 (Real.log ρ / θ)) ∧
    Tendsto (fun n : ℕ => meanAWTAband (pwtLawP n (lam n) μ θ) θ) atTop
        (𝓝 (-(μ * (Real.log ρ / θ)) / (θ * qOf ρ μ θ) + 1 / θ)) ∧
    Tendsto (fun n : ℕ => varPWT (pwtLawP n (lam n) μ θ)) atTop (𝓝 0) := by sorry

end PoolOrNot.Moderate
