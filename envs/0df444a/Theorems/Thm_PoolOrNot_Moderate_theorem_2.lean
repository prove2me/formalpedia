-- Prove2me | Theorems.Thm_PoolOrNot_Moderate_theorem_2
-- name    : PoolOrNot.Moderate.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:40.633583+00:00
-- url     : https://prove2.me/theorems/347aa5e5-99a9-4144-a800-6a1184c128ba
-- title:
--   Theorem 2, p. 7 — q* is the unique invariant state in 𝕊_N and attracts every fluid path at rate e^{−θt}
-- statement:
--   Let $\mu, \theta > 0$, $\rho > 1$, and $N > \bar q + 1$ as in (19). Then $q^* \in \mathbb S_N$, $q^*$ is an invariant state of the fluid model, and it is the only invariant state in $\mathbb S_N$. Moreover, for every fluid solution $(\bar Q, \bar U)$ with $\bar Q(0) \in \mathbb S_N$ there is $c > 0$ such that
--   $$|\bar Q_i(t) - q^*_i| \le c\, e^{-\theta t} \qquad \text{for } i = 1, \dots, N-1 \text{ and } t \ge 0. \tag{20}$$
--
--   In particular $\lim_{t \to \infty} \bar Q(t) = q^*$: the invariant state is the limiting state of the fluid model, which Theorem 3(ii) transfers to the stationary laws of the stochastic systems.
--
--   **Formalization Note** An invariant state is one for which the constant path is a fluid solution (p. 7: "With $\bar Q(0) = q^*$ and $\rho > 1$, the fluid solution is given by $\bar Q(t) = q^*$"); uniqueness compares coordinates $i \ge 1$. The constant $c$ may depend on the solution.
-- source:
--   Cao, He, Huang & Liu, To Pool or Not to Pool: Queueing Design for Large-Scale Service Systems, Operations Research, Articles in Advance (2020), doi:10.1287/opre.2019.1976, p. 7 (PDF 8), Theorem 2, (20)

import Mathlib
import Definitions.Def_PoolOrNot_Moderate_Chain
import Definitions.Def_PoolOrNot_Moderate_Fluid

namespace PoolOrNot.Moderate

/-- **Theorem 2**, p. 7. Assume `ρ > 1` and (19). Then `q*` is the unique invariant state in `𝕊_N`,
and every fluid solution started in `𝕊_N` converges to it exponentially:
`|Q̄_i(t) − q*_i| ≤ c e^{−θt}` for `i = 1, …, N − 1`, `t ≥ 0`, for some `c > 0` ((20)). -/
theorem theorem_2 (ρ μ θ : ℝ) (hρ : 1 < ρ) (hμ : 0 < μ) (hθ : 0 < θ) (N : ℕ)
    (hN : qBar ρ μ θ + 1 < N) :
    InSN N (qStar ρ μ θ) ∧ IsInvariantState ρ μ θ (qStar ρ μ θ) ∧
    (∀ x : ℕ → ℝ, InSN N x → IsInvariantState ρ μ θ x → ∀ i : ℕ, 1 ≤ i → x i = qStar ρ μ θ i) ∧
    ∀ Q U : ℕ → ℝ → ℝ, IsFluidSolution ρ μ θ Q U → InSN N (fun i => Q i 0) →
      ∃ c : ℝ, 0 < c ∧ ∀ i : ℕ, 1 ≤ i → i ≤ N - 1 → ∀ t : ℝ, 0 ≤ t →
        |Q i t - qStar ρ μ θ i| ≤ c * Real.exp (-θ * t) := by sorry

end PoolOrNot.Moderate
