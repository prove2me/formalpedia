-- Prove2me | Theorems.Thm_PoolOrNot_Moderate_theorem_4
-- name    : PoolOrNot.Moderate.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:35.507655+00:00
-- url     : https://prove2.me/theorems/8ed70c8e-d959-47df-b3ef-d2d1d299869c
-- title:
--   Theorem 4, p. 9 — the DQ–JSQ steady-state PWT converges weakly to χ·T_a(q̄) + (1−χ)·T_a(⌊q⌋)
-- statement:
--   Let $\mu, \theta > 0$, $\lambda_n > 0$, and assume (21) with $\rho > 1$. Let $q, \bar q, r$ be as in (18) and let $\chi$ be a Bernoulli random variable with
--   $$p := P(\chi = 1) = \frac{r(\mu + \theta\bar q)}{\rho\mu},$$
--   independent of $T_a(\bar q)$ and $T_a(\lfloor q \rfloor)$. Then $p \in [0, 1]$, and the steady-state potential waiting time $W^n$ of the $n$-th DQ–JSQ system converges in distribution:
--   $$W^n \Rightarrow W := \chi\, T_a(\bar q) + (1 - \chi)\, T_a(\lfloor q \rfloor) \qquad (n \to \infty).$$
--
--   The limit is a two-point mixture: a customer joins a server with $\bar q$ customers with probability about $p$ and one with $\lfloor q \rfloor$ customers otherwise. It yields every DQ–JSQ limit of Theorem 5.
--
--   **Formalization Note** The law of $W$ is $p\,\mathcal L(T_a(\bar q)) + (1-p)\,\mathcal L(T_a(\lfloor q \rfloor))$; weak convergence is convergence of $\int f\,d\mathcal L(W^n)$ for every bounded continuous $f$. $W^n$ is the PWT law of the definition `PoolOrNot.Moderate.Waiting` built from an arbitrary stationary law of the $n$-th chain (unique by Theorem 3(ii)).
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research, Articles in Advance (2020), doi:10.1287/opre.2019.1976, p. 9 (PDF 10), Theorem 4

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Model
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_PoolOrNot_Moderate_Chain
import Definitions.Def_PoolOrNot_Moderate_Waiting

open Filter Topology MeasureTheory BoundedContinuousFunction JSQHalfinWhitt.Tightness

namespace PoolOrNot.Moderate

/-- **Theorem 4**, p. 9. Let `p := r(μ + θq̄)/(ρμ)` and `W := χ·T_a(q̄) + (1 − χ)·T_a(⌊q⌋)` with
`χ ~ Bernoulli(p)` independent of `T_a(q̄)`, `T_a(⌊q⌋)`, i.e. `law W = p·law T_a(q̄) + (1 − p)·law T_a(⌊q⌋)`.
Under (21) with `ρ > 1`, `p ∈ [0, 1]` and the steady-state PWT `Wⁿ` of the `n`-th DQ–JSQ system
converges weakly to `W`. -/
theorem theorem_4 (μ θ ρ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (hθ : 0 < θ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n)
    (h21 : Tendsto (fun n : ℕ => lam n / ((n : ℝ) * μ)) atTop (𝓝 ρ)) (hρ : 1 < ρ)
    (π : (n : ℕ) → State n → ℝ)
    (hπ : ∀ n : ℕ, 1 ≤ n → IsStationaryDist (genAb n (lam n) μ θ) (π n)) :
    0 ≤ pMix ρ μ θ ∧ pMix ρ μ θ ≤ 1 ∧
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n : ℕ => ∫ w, f w ∂(pwtLawD (π n) μ θ)) atTop
        (𝓝 (∫ w, f w ∂(ENNReal.ofReal (pMix ρ μ θ) • taLaw μ θ (qBar ρ μ θ) +
          ENNReal.ofReal (1 - pMix ρ μ θ) • taLaw μ θ ⌊qOf ρ μ θ⌋₊))) := by sorry

end PoolOrNot.Moderate
