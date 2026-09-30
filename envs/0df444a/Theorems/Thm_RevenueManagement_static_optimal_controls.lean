-- Prove2me | Theorems.Thm_RevenueManagement_static_optimal_controls
-- name    : RevenueManagement.static_optimal_controls
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:30:01.096296+00:00
-- url     : https://prove2.me/theorems/33884532-de57-45b8-a02b-2b01f9ba37f7
-- title:
--   Theorem 2.1: the static model is optimally controlled by nested protection levels (2.4)-(2.5), by nested booking limits (2.6), or by bid-price tables (2.7)
-- statement:
--   For the static model (2.3) with prices $p_1 \ge p_2 \ge \dots \ge 0$ and pmf demands, and
--   any capacity $C$: the optimal protection levels are nested, $y_j^* \le y_{j+1}^*$ for all
--   $j$; and for every stage $j+1$, remaining capacity $x \le C$ and demand $d$, each of the
--   following decisions attains the inner maximum of the Bellman equation: (i) the
--   protection-level control $u^* = \min\{(x - y_j^*)^+, d\}$ of (2.5); (ii) the booking-limit
--   control $u^* = \min\{(b_{j+1}^* - (C - x))^+, d\}$ with $b_{j+1}^* = C - y_j^*$ of (2.6);
--   (iii) the bid-price control that accepts the $z$-th unit while $p_{j+1}$ is at least the
--   bid price $\pi_{j+1}(x + 1 - z) = \Delta V_j(x + 1 - z)$ of (2.7). In (i) and (ii) the
--   positive part is the truncated subtraction of $\mathbb N$.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 38-40, Theorem 2.1 with Eq. (2.4)-(2.7) and the nested structure y1* ≤ y2* ≤ ... ≤ yn-1* of p. 39

import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem static_optimal_controls (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hf : ∀ j, IsPmf (f j))
    (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p) (C : ℕ) :
    (∀ j, protLevel p f C j ≤ protLevel p f C (j + 1)) ∧
    (∀ j x d, x ≤ C → IsStageOptimal p f j x d (min (x - protLevel p f C j) d)) ∧
    (∀ j x d, x ≤ C → IsStageOptimal p f j x d (min (bookLimit p f C (j + 1) - (C - x)) d)) ∧
    (∀ j x d, x ≤ C → IsStageOptimal p f j x d (bidControl p f j x d)) := by sorry

end RevenueManagement
