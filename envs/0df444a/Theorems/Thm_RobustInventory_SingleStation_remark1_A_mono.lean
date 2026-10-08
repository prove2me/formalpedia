-- Prove2me | Theorems.Thm_RobustInventory_SingleStation_remark1_A_mono
-- name    : RobustInventory.SingleStation.remark1_A_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:32:14.798478+00:00
-- url     : https://prove2.me/theorems/dca782cc-8a72-4490-8e21-f5709b562705
-- title:
--   §3.1, Remark 1 after Theorem 3.2, p. 156 — $A_{k-1} \le A_k$, so $w'_k \ge \bar w_k$ iff $p \ge h$
-- statement:
--   In the single-station model, let $A_k$ be the optimal value of LP (13), with $A_{-1} = 0$, and $w'$ the modified demand (20). Then:
--
--   1. $A_{k-1} \le A_k$ for every $k \ge 0$;
--   2. if $p \ge h$, then $w'_k \ge \bar w_k$ for every $k$;
--   3. if $p \le h$, then $w'_k \le \bar w_k$ for every $k$.
--
--   When shortage is more expensive than holding, the robust policy raises the safety stock; when holding is more expensive, it lowers it. In particular, when $p \ge h$ and the nominal demands are nonnegative, the modified demand is nonnegative, which is the hypothesis under which part (b) of Theorem 3.2 is stated.
--
--   **Formalization Note** The page says $w'_k$ is "greater than" $\bar w_k$ if $p > h$ and "smaller" if $p < h$; these hold only weakly, since $A_k = A_{k-1}$ is possible (for example $\hat w_k = 0$ and $\Gamma_k = \Gamma_{k-1}$), so the statement uses $\ge$ and $\le$. The case $p = h$ ($w'_k = \bar w_k$) is the intersection of 2 and 3.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), p. 156 (PDF 7), §3.1, Remark 1 after Theorem 3.2

import Definitions.Def_RobustInventory_SingleStation_Deviation

namespace RobustInventory.SingleStation

/-- §3.1, Remark 1 after Theorem 3.2, p. 156: `A_{k-1} ≤ A_k` for all `k` (with `A_{-1} = 0`);
hence the modified demand satisfies `w'_k ≥ w̄_k` for all `k` if `p ≥ h`, and `w'_k ≤ w̄_k`
for all `k` if `p ≤ h`. -/
theorem remark1_A_mono (M : Model) :
    (∀ k, M.Aprev k ≤ M.A k) ∧
    (M.h ≤ M.p → ∀ k, M.wbar k ≤ M.wmod k) ∧
    (M.p ≤ M.h → ∀ k, M.wmod k ≤ M.wbar k) := by sorry

end RobustInventory.SingleStation
