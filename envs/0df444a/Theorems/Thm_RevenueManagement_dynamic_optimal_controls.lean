-- Prove2me | Theorems.Thm_RevenueManagement_dynamic_optimal_controls
-- name    : RevenueManagement.dynamic_optimal_controls
-- status  : Disproved
-- author  : @naimengye
-- created : 2026-09-24T00:31:46.37799+00:00
-- url     : https://prove2.me/theorems/17a01598-9530-4f1b-8313-c525f9159e94
-- title:
--   Theorem 2.2: the dynamic model is optimally controlled by time-dependent nested protection levels (2.19), booking limits (2.20), or bid-price tables (2.18)
-- statement:
--   For the dynamic model (2.17) with an arrival model, prices $p_1 \ge \dots \ge p_n \ge 0$,
--   capacity $C$ and a period $1 \le t \le T$: the time-dependent protection levels are nested,
--   $y_j^*(t) \le y_{j+1}^*(t)$; and for a class-$j$ request ($1 \le j \le n$) with
--   $1 \le x \le C$ units remaining, each of the following accept/reject decisions maximizes
--   $(p_j - \Delta V_{t+1}(x))\,u$ over $u \in \{0, 1\}$: (i) accept iff $x > y_{j-1}^*(t)$,
--   the protection levels (2.19); (ii) accept iff $C - x < b_j^*(t)$, the booking limits
--   (2.20); (iii) accept iff $p_j \ge \pi_{t+1}(x)$, the bid prices (2.18).
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 59-61, Theorem 2.2 with Eq. (2.18)-(2.20) and the acceptance rule p_j ≥ ΔV_{t+1}(x) of Sect. 2.5.2

import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem dynamic_optimal_controls (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T C : ℕ)
    (hlam : IsArrivalModel lam n) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p) (t : ℕ) (ht : 1 ≤ t)
    (htT : t ≤ T) :
    (∀ j, dynProtLevel lam p n T C t j ≤ dynProtLevel lam p n T C t (j + 1)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if dynProtLevel lam p n T C t (j - 1) < x then 1 else 0)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if C - x < dynBookLimit lam p n T C t j then 1 else 0)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if dynBidPrice lam p n T (t + 1) x ≤ p j then 1 else 0)) := by sorry

end RevenueManagement
