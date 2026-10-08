-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_lemma_3_1_b
-- name    : RobustInventory.SingleStation.lemma_3_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:09:35.985056+00:00
-- url     : https://prove2.me/theorems/caa26541-32bd-4155-b14c-9f1182e6b3b9
-- title:
--   Lemma 3.1(b), p. 154 — without fixed cost, order-up-to $S_k = w_k$ is optimal for the nominal problem
-- statement:
--   Consider the single-station model without fixed cost ($K = 0$) and a demand sequence $w$ with $w_k \ge 0$ for $k < T$. Let $u$ be the order-up-to policy with thresholds $S_k = w_k$, run along its own trajectory: $x_0$ is the initial stock, and in period $k$ one orders
--   $$u_k = \begin{cases} w_k - x_k & \text{if } x_k < w_k,\\ 0 & \text{otherwise,}\end{cases}\qquad x_{k+1} = x_k + u_k - w_k.$$
--   Then $u$ is optimal for the nominal problem with demand $w$: it minimizes $\sum_{k=0}^{T-1}\big(c\,u_k + \max(h x_{k+1}, -p x_{k+1})\big)$ over all order sequences with $u_k \ge 0$.
--
--   The paper states this for the nominal demand $\bar w$; the proof of Theorem 3.2 applies it to the modified demand $w'$, so it is stated here for an arbitrary nonnegative demand sequence.
--
--   **Formalization Note** The hypothesis $w_k \ge 0$ is the paper's nonnegativity of demand (p. 156: "the demand is always nonnegative"). It is necessary: for a negative demand the order-up-to policy is not optimal in general (see the Formalization Note of the goal theorem for an instance). The paper's proof assumes $I < T-1$, "otherwise the problem is trivial"; the statement has no such restriction.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 154 (PDF 5), §3.1, Lemma 3.1(b) and Definition 3.1

import Definitions.Def_RobustInventory_SingleStation_Model

namespace RobustInventory.SingleStation

/-- Lemma 3.1(b), p. 154: without fixed cost (`K = 0`), for a nonnegative demand sequence `w`,
the order-up-to policy with thresholds `S_k = w_k`, run along its own trajectory from `x₀`
(order `w_k - x_k` if `x_k < w_k`, nothing otherwise), is optimal for the nominal problem
with demand `w`. -/
theorem lemma_3_1_b (M : Model) (hK : M.K = 0) (w : ℕ → ℝ) (hw : ∀ k < M.T, 0 ≤ w k) :
    M.IsNominalOptimal w (orderUpTo M.x0 w w) := by sorry

end RobustInventory.SingleStation
