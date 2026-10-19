-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_ineq_13
-- name    : TradingPostNSW.Leontief.ineq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:09.770436+00:00
-- url     : https://prove2.me/theorems/a3e411f6-98f4-4f9b-90a7-b67d8cd266a9
-- title:
--   Inequality (13), p. 22 — Π_i u_i(y_i)^{B_i} ≤ Π_i (B_i / φ_i(p))^{B_i} for prices summing to the total budget
-- statement:
--   Consider a Fisher market with Leontief valuations satisfying the standing assumptions, and prices $p \ge 0$ with $\sum_j p_j = \sum_i B_i$ and $\phi_i(p) = \sum_j v_{i,j} p_j > 0$ for every agent $i$. Then every feasible allocation $y$ satisfies
--   $$\prod_{i=1}^n u_i(y_i)^{B_i} \;\le\; \prod_{i=1}^n \Big( \frac{B_i}{\phi_i(p)} \Big)^{B_i}.$$
--
--   On the page this is the step that compares the optimal Nash social welfare with the dual objective of the Eisenberg–Gale program at the $\epsilon$-equilibrium prices $p'$, a feasible dual solution.
--
--   **Formalization Note** The page states (13) for the optimal allocation $x^*$ (an exact market equilibrium) and the $\epsilon$-equilibrium prices $p'$. It is stated here for every feasible allocation $y$ and every price vector with the two properties the page uses for $p'$: total price equal to total budget (the previous milestone) and $\phi_i(p') > 0$. Since $x^*$ maximizes the left side over feasible allocations, this is equivalent and avoids an existence theorem for the optimum. Powers are real powers of nonnegative bases.
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 22, proof of Theorem 4.8, Inequality (13)

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

namespace TradingPostNSW.Leontief

/-- Inequality (13), p. 22: for prices `p ≥ 0` summing to the total budget with every
`φ_i(p) > 0`, every feasible allocation `y` satisfies
`Π_i u_i(y_i)^{B_i} ≤ Π_i (B_i / φ_i(p))^{B_i}`. -/
theorem ineq_13 {n m : ℕ} (I : Instance n m) (hI : Standing I) (p : Fin m → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = ∑ i, I.B i) (hφ : ∀ i, 0 < phi I i p)
    (y : Fin n → Fin m → ℝ) (hy : Feasible I y) :
    ∏ i, (u I i (y i)) ^ (I.B i) ≤ ∏ i, (I.B i / phi I i p) ^ (I.B i) := by sorry

end TradingPostNSW.Leontief
