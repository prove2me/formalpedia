-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_eq_14
-- name    : TradingPostNSW.Leontief.eq_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:28.618837+00:00
-- url     : https://prove2.me/theorems/6052cd96-44ed-4268-be19-b57984560f04
-- title:
--   Equation (14), p. 22 — the optimal Leontief utility affordable at prices p is B_i / φ_i(p)
-- statement:
--   Consider a Fisher market with Leontief valuations satisfying the standing assumptions, prices $p \ge 0$, and an agent $i$ with $\phi_i(p) = \sum_j v_{i,j} p_j > 0$. Then the largest Leontief utility agent $i$ can afford with its budget is attained and equals
--   $$u_i(p) \;=\; \max\{ u_i(y) \mid y \ge 0,\ p \cdot y \le B_i \} \;=\; \frac{B_i}{\phi_i(p)}.$$
--
--   $\phi_i(p)$ is the price of one unit of utility for agent $i$, so its budget buys $B_i/\phi_i(p)$ units. This formula turns the $\epsilon$-optimality clause of an $\epsilon$-market equilibrium into the bound $B_i/\phi_i(p) \le (1+\epsilon) u_i(x_i)$.
--
--   **Formalization Note** The page states (14) at the $\epsilon$-equilibrium prices $p'$, writing $\phi(p')$ for $\phi_i(p')$; it is stated here for all prices $p \ge 0$ with $\phi_i(p) > 0$, a positivity the page uses implicitly. The maximum is rendered with `IsGreatest`.
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 22, proof of Theorem 4.8, Equation (14)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

namespace TradingPostNSW.Leontief

/-- Equation (14), p. 22: at prices `p ≥ 0` with `φ_i(p) > 0`, the optimal Leontief utility agent
`i` can afford with budget `B_i` is `B_i / φ_i(p)`. -/
theorem eq_14 {n m : ℕ} (I : Instance n m) (hI : Standing I) (p : Fin m → ℝ)
    (hp : ∀ j, 0 ≤ p j) (i : Fin n) (hφ : 0 < phi I i p) :
    IsGreatest {t : ℝ | ∃ y : Fin m → ℝ, (∀ j, 0 ≤ y j) ∧ ∑ j, p j * y j ≤ I.B i ∧ t = u I i y}
      (I.B i / phi I i p) := by sorry

end TradingPostNSW.Leontief
