-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_robust_pair_iff
-- name    : RobustInventory.SingleStation.robust_pair_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:31:44.100369+00:00
-- url     : https://prove2.me/theorems/ade8dade-0a48-4259-83f2-089ea61c336f
-- title:
--   §3.1, (10)–(11) → (14), pp. 153–154 — robust counterpart of the $k$-th holding/shortage pair
-- statement:
--   Fix the single-station model, a period $k$, an order sequence $u$ and a real number $y$. For scaled deviations $z$ write $w_i = \bar w_i + \hat w_i z_i$ for the demand and $x_{k+1}(z) = x_0 + \sum_{i=0}^{k}(u_i - w_i)$ for the resulting stock. The following are equivalent.
--
--   1. For every $z$ with $|z_i| \le 1$ ($i \le k$) and $\sum_{i=0}^{k}|z_i| \le \Gamma_k$, the holding and shortage constraints (10)–(11) of period $k$ hold:
--   $$y \ge h\,x_{k+1}(z),\qquad y \ge -p\,x_{k+1}(z).$$
--   2. There are $q \ge 0$ and $r_i \ge 0$ with $q + r_i \ge \hat w_i$ ($i \le k$) such that
--   $$y \ge h\Big(\bar x_{k+1} + q\Gamma_k + \sum_{i=0}^{k} r_i\Big),\qquad y \ge p\Big(-\bar x_{k+1} + q\Gamma_k + \sum_{i=0}^{k} r_i\Big),$$
--   where $\bar x_{k+1} = x_0 + \sum_{i=0}^{k}(u_i - \bar w_i)$.
--
--   This is the instance, for the inventory problem, of the robust counterpart of Bertsimas and Sim (Theorem 2.1 of the paper): it shows that the constraints of (14) are exactly the $k$-th pair (10)–(11) protected against every deviation within the budget $\Gamma_k$.
--
--   **Formalization Note** The deviation set is the one of LP (13): it uses the budget $\Gamma_k$ of period $k$ only, as formulation (14) does, and not the intersection of all budgets $\Gamma_0,\dots,\Gamma_k$ in the paper's set $\mathcal P$ (under $\mathcal P$ only the implication 2 ⇒ 1 holds). The page writes $x_{k+1} = \bar x_{k+1} + \sum \hat w_i z_i$; since $w_i = \bar w_i + \hat w_i z_i$ the correct sign is $x_{k+1} = \bar x_{k+1} - \sum \hat w_i z_i$, which is what the statement uses (the deviation set is symmetric, so the slip does not affect the result).
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), pp. 153–154 (PDF 4–5), §3.1, Eqs. (10)–(11), (13), (14) and Remark 1 after (13); p. 152 (PDF 3), Theorem 2.1

import Definitions.Def_RobustInventory_SingleStation_Deviation

namespace RobustInventory.SingleStation

open Finset

/-- §3.1, (10)–(11) → (14), pp. 153–154 (the instance of Theorem 2.1): for a period `k`, an
order sequence `u` and a value `y`, the `k`-th pair of holding/shortage constraints (10)–(11)
holds for every demand `w_i = w̄_i + ŵ_i z_i` with `|z_i| ≤ 1` and `∑_{i=0}^{k} |z_i| ≤ Γ_k`
if and only if there are dual variables `q ≥ 0`, `r_i ≥ 0`, `q + r_i ≥ ŵ_i` (`i ≤ k`) with
`y ≥ h (x̄_{k+1} + q Γ_k + ∑ r_i)` and `y ≥ p (-x̄_{k+1} + q Γ_k + ∑ r_i)`. -/
theorem robust_pair_iff (M : Model) (k : ℕ) (u : ℕ → ℝ) (y : ℝ) :
    (∀ z : ℕ → ℝ, (∀ i ≤ k, |z i| ≤ 1) → ∑ i ∈ range (k + 1), |z i| ≤ M.Γ k →
      M.h * M.stock (fun i => M.wbar i + M.what i * z i) u k ≤ y ∧
      -(M.p * M.stock (fun i => M.wbar i + M.what i * z i) u k) ≤ y) ↔
    (∃ (q : ℝ) (r : ℕ → ℝ), M.LP13DualFeasible k q r ∧
      M.h * (M.xbar u k + q * M.Γ k + ∑ i ∈ range (k + 1), r i) ≤ y ∧
      M.p * (-M.xbar u k + q * M.Γ k + ∑ i ∈ range (k + 1), r i) ≤ y) := by sorry

end RobustInventory.SingleStation
