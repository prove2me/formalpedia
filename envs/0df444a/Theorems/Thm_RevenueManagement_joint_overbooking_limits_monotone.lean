-- Prove2me | Theorems.Thm_RevenueManagement_joint_overbooking_limits_monotone
-- name    : RevenueManagement.joint_overbooking_limits_monotone
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:41:40.055277+00:00
-- url     : https://prove2.me/theorems/5777a15d-4d80-451a-b929-5bb28148fac6
-- title:
--   Sect. 4.5.2: by submodularity of G, the greatest optimal booking limit of class i is nonincreasing in the booking level of any other class j
-- statement:
--   In the substitutable-capacity model with nonnegative capacities and Poisson show demands
--   with means $q_j x_j$, $q_j \ge 0$: for classes $i \ne j$ and any levels $x$, the greatest
--   optimal booking limit of class $i$ when class $j$ is held one unit higher, at $x_j + 1$, is
--   at most the greatest optimal booking limit of class $i$ at $x$ (in
--   $\mathbb N \cup \{\infty\}$). This is the consequence of Proposition 4.4 that the book draws
--   in the paragraph following it.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 164, the paragraph after Proposition 4.4 ('The submodularity property implies that the optimal booking limit for class j is nonincreasing in the booking limit for any other class i ≠ j')

import Definitions.Def_RevenueManagement_overbooking

namespace RevenueManagement

theorem joint_overbooking_limits_monotone {n m : ℕ} (h : Fin n → Fin (m + 1) → ℝ)
    (Cap : Fin (m + 1) → ℝ) (hCap : ∀ i, 0 ≤ Cap i) (p s q : Fin n → ℝ) (hq : ∀ j, 0 ≤ q j)
    (y x : Fin n → ℕ) (i j : Fin n) (hij : i ≠ j) :
    jointLimit h Cap p s q y (x + Pi.single j 1) i ≤ jointLimit h Cap p s q y x i := by sorry

end RevenueManagement
