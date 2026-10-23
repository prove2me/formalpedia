-- Prove2me | Theorems.Thm_PoolOrNot_Moderate_theorem_3_ii
-- name    : PoolOrNot.Moderate.theorem_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:46.407345+00:00
-- url     : https://prove2.me/theorems/f7edbc7c-6596-4018-b61d-e024b79c9489
-- title:
--   Theorem 3(ii), p. 9 — the n-th DQ–JSQ chain has a unique stationary law and Q̄ⁿ(∞) ⇒ q* in ℝ^∞
-- statement:
--   Let $\mu, \theta > 0$, let $\lambda_n > 0$ be the arrival rate of the $n$-th DQ–JSQ system, and assume (21):
--   $$\lim_{n \to \infty} \frac{\lambda_n}{n\mu} = \rho > 1.$$
--   Then:
--
--   1. for each $n \ge 1$ the $n$-server DQ–JSQ chain has exactly one stationary distribution, the law of $Q^n(\infty)$;
--   2. the fluid-scaled stationary state $\bar Q^n(\infty) = Q^n(\infty)/n$ converges to the invariant state $q^*$ in $\mathbb R^\infty$: for every $\varepsilon > 0$,
--   $$\lim_{n \to \infty} P\bigl(d(\bar Q^n(\infty), q^*) > \varepsilon\bigr) = 0 .$$
--
--   This is the interchange of limits that justifies using $q^*$ as the steady-state approximation of the many-server system.
--
--   **Formalization Note** The page asserts that $\bar Q^n(t) \Rightarrow \bar Q^n(\infty)$ as $t \to \infty$; the transient law is not fixed on the page, so part 1 states the equivalent steady-state content: the stationary law exists and is unique, as a probability solution of the global balance equations $\pi\mathcal G = 0$ of the published `IsStationaryDist`. The chain has unbounded rates but is non-explosive (arrivals are Poisson), so these are its stationary laws. Part 2 is convergence in probability to a constant, which is equivalent to weak convergence to the Dirac law at $q^*$. The convergence statement is made for every family of stationary laws.
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research, Articles in Advance (2020), doi:10.1287/opre.2019.1976, p. 9 (PDF 10), Theorem 3(ii); (21) and d on p. 8 (PDF 9)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_PoolOrNot_Moderate_Chain

open Filter Topology JSQHalfinWhitt.Tightness

namespace PoolOrNot.Moderate

/-- **Theorem 3(ii)**, p. 9, steady-state reading. Under (21) with `ρ > 1`: (a) for each `n ≥ 1` the
`n`-server DQ–JSQ chain has exactly one stationary law `Q̄ⁿ(∞)`; (b) for any family of stationary
laws `πₙ`, `Q̄ⁿ(∞) = Qⁿ(∞)/n` converges in probability (hence weakly) to the constant `q*` in the
metric `d` of `ℝ^∞`. -/
theorem theorem_3_ii (μ θ ρ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n)
    (h21 : Tendsto (fun n : ℕ => lam n / ((n : ℝ) * μ)) atTop (𝓝 ρ)) (hρ : 1 < ρ) :
    (∀ n : ℕ, 1 ≤ n → ∃! π : State n → ℝ, IsStationaryDist (genAb n (lam n) μ θ) π) ∧
    ∀ π : (n : ℕ) → State n → ℝ, (∀ n : ℕ, 1 ≤ n → IsStationaryDist (genAb n (lam n) μ θ) (π n)) →
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => prob (π n) (fun q => ε < dInf (fluidScaled q) (qStar ρ μ θ)))
          atTop (𝓝 0) := by sorry

end PoolOrNot.Moderate
