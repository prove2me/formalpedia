-- Prove2me | Theorems.Thm_RobustMDP_Discounted_discountedCost_lp
-- name    : RobustMDP.Discounted.discountedCost_lp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:59:11.625061+00:00
-- url     : https://prove2.me/theorems/b6e72bb8-671a-4b66-af0f-6df761a282c7
-- title:
--   Eq. (26), p. 786 — the discounted cost of a stationary policy is the value of a linear program
-- statement:
--   Fix an initial state $i_0$, a stationary control policy $\pi = (\mathbf a, \mathbf a, \dots)$ and a stationary policy of nature $(P^a)_{a \in \mathcal A}$ with rows $P^a(i, \cdot) \in \mathcal P_i^a$. Let $q = e_{i_0}$, that is $q(i_0) = 1$ and $q(i) = 0$ for $i \neq i_0$. Then the discounted cost $C_\infty(\pi, \tau)$ is the optimal value of the linear program
--   $$\max_v \; q^T v \quad \text{s.t.} \quad v(i) \le c(i, \mathbf a(i)) + \nu \sum_j P^{\mathbf a(i)}(i, j)\, v(j), \quad i \in \mathcal X, \tag{26}$$
--   and the maximum is attained.
--
--   This connects the probabilistic cost, defined as an expected discounted sum along the Markov chain, to the linear inequalities the proof of Theorem 3 manipulates.
--
--   **Formalization Note** $q^T v$ is written $v(i_0)$. The statement is `IsGreatest` of the set of values $v(i_0)$ over feasible $v$.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 786, Eq. (26) (with q defined below Eq. (25))

import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Discounted_discountedCost

namespace RobustMDP.Discounted

/-- Linear program (26) (Nilim–El Ghaoui 2005, p. 786). For a stationary controller policy
`π = (𝐚, 𝐚, …)` and a fixed stationary nature policy `P ∈ 𝒯_s`, the discounted cost
`C_∞(π, P)` from the initial state `i₀` is the optimal value of
`max_v qᵀ v  s.t.  v(i) ≤ c(i, 𝐚(i)) + ν ∑_j P^{𝐚(i)}(i, j) v(j), i ∈ 𝒳`,
with `q = e_{i₀}` (so `qᵀ v = v(i₀)`), and the maximum is attained. -/
theorem discountedCost_lp {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n)
    (π : StationaryPolicy n A) (P : M.StationaryNature) :
    IsGreatest
      ((fun v : Fin n → ℝ => v i₀) ''
        {v | ∀ i, v i ≤ M.cost i (π i) + M.discount * ∑ j, P.1 (π i) i j * v j})
      (M.discountedCost i₀ π P) := by sorry

end RobustMDP.Discounted
