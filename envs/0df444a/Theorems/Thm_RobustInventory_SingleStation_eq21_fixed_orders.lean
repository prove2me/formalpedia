-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_eq21_fixed_orders
-- name    : RobustInventory.SingleStation.eq21_fixed_orders
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:32:03.20474+00:00
-- url     : https://prove2.me/theorems/8971b2bd-a558-4ab9-9f54-16a209a0f9fe
-- title:
--   §3.1, Eq. (21), p. 155 — the value of (14) for fixed orders
-- statement:
--   Fix the single-station model and an order sequence $u$ with $u_k \ge 0$ for $k < T$. Let $A_k$ be the optimal value of LP (13) and $\bar x_{k+1} = x_0 + \sum_{i=0}^{k}(u_i - \bar w_i)$. Then the minimum of the objective of the robust formulation (14) over the remaining variables $(y, q, r)$ that are feasible together with $u$ is
--   $$\sum_{k=0}^{T-1}\Big[c\,u_k + K\,\mathbf 1_{\{u_k > 0\}} + \max\big(h(\bar x_{k+1} + A_k),\ p(-\bar x_{k+1} + A_k)\big)\Big],$$
--   in the sense that every feasible $(y, q, r)$ gives an objective at least this value and some feasible $(y, q, r)$ attains it.
--
--   This is the reduction (21) in the proof of Theorem 3.2: once the dual variables are chosen optimally, the robust problem becomes a problem in the orders alone.
--
--   **Formalization Note** The paper's (21) is stated with $A_k = q^*_k\Gamma_k + \sum_i r^*_{ik}$ for an optimal solution of (14); here $A_k$ is the value of (13), and the statement is the value of (14) for each fixed $u$, which is what the proof uses.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 155 (PDF 6), §3.1, proof of Theorem 3.2, Eq. (21)

import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust

namespace RobustInventory.SingleStation

open Finset

/-- §3.1, Eq. (21), p. 155: for a fixed nonnegative order sequence `u`, the optimal value of the
robust formulation (14) over the remaining variables `(y, q, r)` is
`∑_{k=0}^{T-1} [C(u_k) + max(h(x̄_{k+1} + A_k), p(-x̄_{k+1} + A_k))]`, and it is attained. -/
theorem eq21_fixed_orders (M : Model) (u : ℕ → ℝ) (hu : ∀ k < M.T, 0 ≤ u k) :
    (∀ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.RobustFeasible u y q r →
      ∑ k ∈ range M.T,
          (M.C (u k) + max (M.h * (M.xbar u k + M.A k)) (M.p * (-M.xbar u k + M.A k)))
        ≤ M.robustObjective u y) ∧
    (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.RobustFeasible u y q r ∧
      M.robustObjective u y = ∑ k ∈ range M.T,
          (M.C (u k) + max (M.h * (M.xbar u k + M.A k)) (M.p * (-M.xbar u k + M.A k)))) := by sorry

end RobustInventory.SingleStation
