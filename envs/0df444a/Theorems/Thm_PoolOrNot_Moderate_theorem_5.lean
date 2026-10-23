-- Prove2me | Theorems.Thm_PoolOrNot_Moderate_theorem_5
-- name    : PoolOrNot.Moderate.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:13.20878+00:00
-- url     : https://prove2.me/theorems/b38db1c2-592a-4748-81e7-02f3fcf449b9
-- title:
--   Theorem 5, pp. 10–11 — moderate overload: DQ–JSQ vs M/M/n+M limits of occupancy, abandonment, AWT, delay, conditional waits, PWT variance
-- statement:
--   Let $\mu, \theta > 0$, let $\lambda_n > 0$ be the common arrival rate of the $n$-th DQ–JSQ system (subscript D) and of the $n$-th M/M/n+M system (subscript P), and assume (21) with
--   $$1 < \rho < 1 + \frac{\theta}{\mu}.$$
--   Let $q, \bar q, r$ be as in (18) and $w := \ln(\rho)/\theta$. Let $W^n$ be the steady-state potential waiting time (PWT), $R$ an independent exponential patience time of rate $\theta$, $V^n = W^n \wedge R$ the actual waiting time (AWT), and $\bar X^n(\infty)$ the steady-state number in system divided by $n$. Then:
--
--   1. $\lim E[\bar X^n_D(\infty)] = q + 1 = \lim E[\bar X^n_P(\infty)]$, where $0 < q < 1$;
--   2. $\lim P^n_D(\mathrm{Ab}) = \dfrac{\rho - 1}{\rho} = \lim P^n_P(\mathrm{Ab})$;
--   3. $\lim E[V^n_D] = \dfrac{q}{\rho\mu} = \lim E[V^n_P]$;
--   4. $\lim P^n_D(\mathrm{De}) = \dfrac{r(\mu + \theta)}{\rho\mu} < 1 = \lim P^n_P(\mathrm{De})$;
--   5. $\lim E[W^n_D \mid W^n_D > 0] = \dfrac1\mu > w = \lim E[W^n_P \mid W^n_P > 0]$;
--   6. $\lim E[W^n_D] = \dfrac{r(\mu + \theta)}{\rho\mu^2} > w = \lim E[W^n_P]$;
--   7. $\lim E[V^n_D \mid W^n_D \le R] = \dfrac{r}{\mu + \theta} < w = \lim E[V^n_P \mid W^n_P \le R]$;
--   8. $\lim E[V^n_D \mid W^n_D > R] = \dfrac{1}{\mu + \theta} > -\dfrac{\mu w}{\theta q} + \dfrac1\theta = \lim E[V^n_P \mid W^n_P > R]$;
--   9. $\displaystyle \lim \mathrm{Var}(W^n_D) = \frac{r(\mu + \theta)}{\rho\mu^3}\Bigl(2 - \frac{r(\mu + \theta)}{\rho\mu}\Bigr) > 0 = \lim \mathrm{Var}(W^n_P)$,
--
--   all limits as $n \to \infty$.
--
--   In moderate overload the dedicated design under JSQ matches the pooled design in occupancy, abandonment and mean AWT, while its delay probability stays bounded away from 1; the price is longer and more variable waits for delayed customers.
--
--   **Formalization Note** The DQ–JSQ quantities are computed from an arbitrary stationary law $\pi_n$ of the $n$-th chain (generator `genAb`, unique by Theorem 3(ii)) through the PWT law of the definition `PoolOrNot.Moderate.Waiting`; the M/M/n+M quantities from the explicit stationary law `ErlangA.Abandonment.stationaryDist`, with $P^n_P(\mathrm{Ab})$ and $P^n_P(\mathrm{De})$ the published `probAbandon` and `probWait` (equal to $P(R < W^n_P)$ and $P(W^n_P > 0)$). As a strengthening that rules out Lean's default values ($0$ for a divergent series, a non-integrable function's integral, or an infinite variance), the statement also asserts that for every $n \ge 1$ both PWT laws are probability laws with finite second moment and both mean-occupancy series converge. The positivity of $\mu, \theta, \lambda_n$ is implicit on the page. The PQ limits other than (ii) are attributed on the page to Whitt (2004); they are part of the theorem as printed.
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research, Articles in Advance (2020), doi:10.1287/opre.2019.1976, pp. 10–11 (PDF 11–12), Theorem 5

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_ErlangA_Abandonment_Model
import Definitions.Def_ErlangA_Staffing_Model
import Definitions.Def_PoolOrNot_Moderate_Chain
import Definitions.Def_PoolOrNot_Moderate_Waiting

open Filter Topology MeasureTheory ProbabilityTheory JSQHalfinWhitt.Tightness

namespace PoolOrNot.Moderate

/-- **Theorem 5**, pp. 10–11. Assume (21) with `1 < ρ < 1 + θ/μ`. Compare the `n`-th DQ–JSQ system
(stationary law `πₙ` of `genAb n λₙ μ θ`, PWT law `pwtLawD πₙ`) with the `n`-th `M/M/n + M` system
(stationary law `stationaryDist n λₙ μ θ`, PWT law `pwtLawP n λₙ μ θ`), patience `R ~ Exp(θ)`
independent of the PWT. With `q, q̄, r` as in (18) and `w := ln(ρ)/θ`, parts (i)–(ix) hold; the
first conjunct records that, for every `n ≥ 1`, both PWT laws are probability laws with finite
second moment and both mean occupancies are convergent series. -/
theorem theorem_5 (μ θ ρ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n)
    (h21 : Tendsto (fun n : ℕ => lam n / ((n : ℝ) * μ)) atTop (𝓝 ρ))
    (hρ1 : 1 < ρ) (hρ2 : ρ < 1 + θ / μ)
    (π : (n : ℕ) → State n → ℝ)
    (hπ : ∀ n : ℕ, 1 ≤ n → IsStationaryDist (genAb n (lam n) μ θ) (π n)) :
    -- well-posedness of every quantity below (strengthening guards)
    (∀ n : ℕ, 1 ≤ n →
      IsProbabilityMeasure (pwtLawD (π n) μ θ) ∧
      IsProbabilityMeasure (pwtLawP n (lam n) μ θ) ∧
      Integrable (fun w : ℝ => w ^ 2) (pwtLawD (π n) μ θ) ∧
      Integrable (fun w : ℝ => w ^ 2) (pwtLawP n (lam n) μ θ) ∧
      Summable (fun q : State n => π n q * ((∑' i : ℕ, (q.1 i : ℝ)) / (n : ℝ))) ∧
      Summable (fun k : ℕ => (k : ℝ) * ErlangA.Abandonment.stationaryDist n (lam n) μ θ k)) ∧
    -- (i)
    (0 < qOf ρ μ θ ∧ qOf ρ μ θ < 1 ∧
      Tendsto (fun n : ℕ => meanOccD (π n)) atTop (𝓝 (qOf ρ μ θ + 1)) ∧
      Tendsto (fun n : ℕ => meanOccP n (lam n) μ θ) atTop (𝓝 (qOf ρ μ θ + 1))) ∧
    -- (ii)
    (Tendsto (fun n : ℕ => probAb (pwtLawD (π n) μ θ) θ) atTop (𝓝 ((ρ - 1) / ρ)) ∧
      Tendsto (fun n : ℕ => ErlangA.Abandonment.probAbandon n (lam n) μ θ) atTop
        (𝓝 ((ρ - 1) / ρ))) ∧
    -- (iii)
    (Tendsto (fun n : ℕ => meanAWT (pwtLawD (π n) μ θ) θ) atTop (𝓝 (qOf ρ μ θ / (ρ * μ))) ∧
      Tendsto (fun n : ℕ => meanAWT (pwtLawP n (lam n) μ θ) θ) atTop
        (𝓝 (qOf ρ μ θ / (ρ * μ)))) ∧
    -- (iv)
    (Tendsto (fun n : ℕ => probDelay (pwtLawD (π n) μ θ)) atTop
        (𝓝 (rOf ρ μ θ * (μ + θ) / (ρ * μ))) ∧
      rOf ρ μ θ * (μ + θ) / (ρ * μ) < 1 ∧
      Tendsto (fun n : ℕ => ErlangA.Staffing.probWait n (lam n) μ θ) atTop (𝓝 1)) ∧
    -- (v)
    (Tendsto (fun n : ℕ => meanPWTDelayed (pwtLawD (π n) μ θ)) atTop (𝓝 (1 / μ)) ∧
      Real.log ρ / θ < 1 / μ ∧
      Tendsto (fun n : ℕ => meanPWTDelayed (pwtLawP n (lam n) μ θ)) atTop
        (𝓝 (Real.log ρ / θ))) ∧
    -- (vi)
    (Tendsto (fun n : ℕ => meanPWT (pwtLawD (π n) μ θ)) atTop
        (𝓝 (rOf ρ μ θ * (μ + θ) / (ρ * μ ^ 2))) ∧
      Real.log ρ / θ < rOf ρ μ θ * (μ + θ) / (ρ * μ ^ 2) ∧
      Tendsto (fun n : ℕ => meanPWT (pwtLawP n (lam n) μ θ)) atTop (𝓝 (Real.log ρ / θ))) ∧
    -- (vii)
    (Tendsto (fun n : ℕ => meanAWTServed (pwtLawD (π n) μ θ) θ) atTop
        (𝓝 (rOf ρ μ θ / (μ + θ))) ∧
      rOf ρ μ θ / (μ + θ) < Real.log ρ / θ ∧
      Tendsto (fun n : ℕ => meanAWTServed (pwtLawP n (lam n) μ θ) θ) atTop
        (𝓝 (Real.log ρ / θ))) ∧
    -- (viii)
    (Tendsto (fun n : ℕ => meanAWTAband (pwtLawD (π n) μ θ) θ) atTop (𝓝 (1 / (μ + θ))) ∧
      -(μ * (Real.log ρ / θ)) / (θ * qOf ρ μ θ) + 1 / θ < 1 / (μ + θ) ∧
      Tendsto (fun n : ℕ => meanAWTAband (pwtLawP n (lam n) μ θ) θ) atTop
        (𝓝 (-(μ * (Real.log ρ / θ)) / (θ * qOf ρ μ θ) + 1 / θ))) ∧
    -- (ix)
    (Tendsto (fun n : ℕ => varPWT (pwtLawD (π n) μ θ)) atTop
        (𝓝 ((rOf ρ μ θ * (μ + θ) / (ρ * μ ^ 3)) * (2 - rOf ρ μ θ * (μ + θ) / (ρ * μ)))) ∧
      0 < (rOf ρ μ θ * (μ + θ) / (ρ * μ ^ 3)) * (2 - rOf ρ μ θ * (μ + θ) / (ρ * μ)) ∧
      Tendsto (fun n : ℕ => varPWT (pwtLawP n (lam n) μ θ)) atTop (𝓝 0)) := by sorry

end PoolOrNot.Moderate
