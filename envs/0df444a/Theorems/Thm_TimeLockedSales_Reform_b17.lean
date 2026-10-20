-- Prove2me | Theorems.Thm_TimeLockedSales_Reform_b17
-- name    : TimeLockedSales.Reform.b17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:49.373707+00:00
-- url     : https://prove2.me/theorems/67d924bf-41b8-4586-b288-b7e7f714f57a
-- title:
--   Proof of Proposition 5, p. 42, (B.17) — an optimum of (9) bounds the optimum of LP (11)
-- statement:
--   Let $(r,z)$ attain the optimum $\pi_9$ of formulation (9), and let $\pi_{LP}$ be the attained optimum of LP (11). Setting $y_t^i(n)=z_t(n)r_t^i(n)$ gives a feasible LP array with the same objective, hence
--   $$L(y)=\pi_9=p\sum_{t,n}z_t(n)\bigl(r_t^1(n)+u_nr_t^0(n)\bigr)\leq\pi_{LP}.\tag{B.17}$$
--   This states the forward substitution and optimal-value inequality printed in the proof.
--
--   **Formalization Note.** State probabilities in (9) are nonnegative. The arrays use the paper's $t=1,\ldots,T$ and $n=-(T-1),\ldots,T-1$, with zero support outside this range. The focus-region and standing assumptions are retained.
-- source:
--   Küçükgül, Özer & Wang, Engineering social learning: information design of time-locked sales campaigns for online platforms, submission manuscript (Nov. 2019; published Management Science 2022, doi:10.1287/mnsc.2021.4151), p. 42, proof of Proposition 5, (B.17)

import Mathlib
import Definitions.Def_TimeLockedSales_Reform_Model

namespace TimeLockedSales.Reform

/-- Equation (B.17), p. 42: an optimum of (9) gives a feasible point of (11)
    with the same value, bounding the optimum of (9) by that of (11). -/
theorem b17 (P : Params) (hS : P.Standing) (hR : P.Region)
    (π9 πLP : ℝ)
    (h9 : IsGreatest {J | ∃ r z, Feasible9 P r z ∧ J = obj9 P r z} π9)
    (hLP : IsGreatest {J | ∃ y, FeasibleLP P y ∧ J = objLP P y} πLP)
    (r : ℕ → ℤ → SignType → ℝ) (z : ℕ → ℤ → ℝ)
    (h : Feasible9 P r z ∧ obj9 P r z = π9) :
    FeasibleLP P (fun t n i => z t n * r t n i) ∧
      objLP P (fun t n i => z t n * r t n i) = π9 ∧ π9 ≤ πLP := by sorry

end TimeLockedSales.Reform
