-- Prove2me | Theorems.Thm_TimeLockedSales_Reform_b18
-- name    : TimeLockedSales.Reform.b18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:38.827071+00:00
-- url     : https://prove2.me/theorems/55598f0c-6799-46a3-909f-a1c4cac96b2f
-- title:
--   Proof of Proposition 5, pp. 42–43, (B.18) — an LP optimum bounds the optimum of (9)
-- statement:
--   Let $y$ attain the optimum $\pi_{LP}$ of LP (11), and let $\pi_9$ be the attained optimum of formulation (9). Define $z_t(n)=\sum_i y_t^i(n)$. Whenever $z_t(n)>0$, take $r_t^i(n)=y_t^i(n)/z_t(n)$; when $z_t(n)=0$, take any probability vector satisfying (R). The recovered $(r,z)$ is feasible for (9), and
--   $$\pi_{LP}=p\sum_{t,n}z_t(n)\bigl(r_t^1(n)+u_nr_t^0(n)\bigr)\leq\pi_9.\tag{B.18}$$
--   This states the reverse substitution and optimal-value inequality printed in the proof.
--
--   **Formalization Note.** Only the entries at $t=1,\ldots,T$ and $n=-(T-1),\ldots,T-1$ enter the programs. At zero state mass, the recovery condition requires an (R)-vector and imposes no ratio. The standing and focus-region assumptions match the section.
-- source:
--   Küçükgül, Özer & Wang, Engineering social learning: information design of time-locked sales campaigns for online platforms, submission manuscript (Nov. 2019; published Management Science 2022, doi:10.1287/mnsc.2021.4151), pp. 42–43, proof of Proposition 5, (B.18)

import Mathlib
import Definitions.Def_TimeLockedSales_Reform_Model

namespace TimeLockedSales.Reform

/-- Equation (B.18), pp. 42–43: an optimum of (11) recovers a feasible point
    of (9) with the same value, bounding the optimum of (11) by that of (9). -/
theorem b18 (P : Params) (hS : P.Standing) (hR : P.Region)
    (π9 πLP : ℝ)
    (h9 : IsGreatest {J | ∃ r z, Feasible9 P r z ∧ J = obj9 P r z} π9)
    (hLP : IsGreatest {J | ∃ y, FeasibleLP P y ∧ J = objLP P y} πLP)
    (y r : ℕ → ℤ → SignType → ℝ)
    (hy : FeasibleLP P y ∧ objLP P y = πLP) (hr : Recovers P y r) :
    Feasible9 P r (zOf y) ∧ obj9 P r (zOf y) = πLP ∧ πLP ≤ π9 := by sorry

end TimeLockedSales.Reform
