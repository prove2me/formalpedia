-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_aux_lp_duality
-- name    : RobustInventory.SingleStation.aux_lp_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:31:17.897371+00:00
-- url     : https://prove2.me/theorems/7e128096-fc94-478b-b88f-6ab694fb9b15
-- title:
--   §3.1, LP (13), pp. 153–154 — the auxiliary LP and its dual are both attained with value $A_k$
-- statement:
--   Consider the single-station model with budgets $\Gamma_k \ge 0$ and deviations $\hat w_i \ge 0$, and let $A_k$ be the optimal value of the auxiliary linear program (13) of period $k$. Then:
--
--   1. the maximum in (13) is attained: there is $z$ with $0 \le z_i \le 1$ ($i \le k$) and $\sum_{i\le k} z_i \le \Gamma_k$ such that $\sum_{i \le k}\hat w_i z_i = A_k$;
--   2. every feasible $z$ of (13) has $\sum_{i\le k}\hat w_i z_i \le A_k$;
--   3. the dual problem is attained with the same value: there are $q \ge 0$ and $r_i \ge 0$ with $q + r_i \ge \hat w_i$ ($i \le k$) and
--   $$q\,\Gamma_k + \sum_{i=0}^{k} r_i = A_k;$$
--   4. every dual feasible $(q, r)$ has $q\,\Gamma_k + \sum_{i\le k} r_i \ge A_k$.
--
--   This is the strong duality step by which the paper passes from the uncertain constraints (10)–(11) to the robust formulation (14), and it identifies the quantity $A_k$ that appears in the modified demand and in the extra cost of Theorem 3.2.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), pp. 153–154 (PDF 4–5), §3.1, LP (13) and the strong-duality sentence after it

import Definitions.Def_RobustInventory_SingleStation_Deviation

namespace RobustInventory.SingleStation

open Finset

/-- §3.1, LP (13) and strong duality (pp. 153–154): for every period `k`, the maximum of the
auxiliary linear program (13) is attained and equals `A_k`, and its dual
`min {q Γ_k + ∑_{i=0}^{k} r_i : q ≥ 0, r_i ≥ 0, q + r_i ≥ ŵ_i}` is attained with the same value. -/
theorem aux_lp_duality (M : Model) (k : ℕ) :
    (∃ z : ℕ → ℝ, M.LP13Feasible k z ∧ ∑ i ∈ range (k + 1), M.what i * z i = M.A k) ∧
    (∀ z : ℕ → ℝ, M.LP13Feasible k z → ∑ i ∈ range (k + 1), M.what i * z i ≤ M.A k) ∧
    (∃ (q : ℝ) (r : ℕ → ℝ), M.LP13DualFeasible k q r ∧
      q * M.Γ k + ∑ i ∈ range (k + 1), r i = M.A k) ∧
    (∀ (q : ℝ) (r : ℕ → ℝ), M.LP13DualFeasible k q r →
      M.A k ≤ q * M.Γ k + ∑ i ∈ range (k + 1), r i) := by sorry

end RobustInventory.SingleStation
