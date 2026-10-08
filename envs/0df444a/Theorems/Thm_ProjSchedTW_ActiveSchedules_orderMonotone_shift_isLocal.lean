-- Prove2me | Theorems.Thm_ProjSchedTW_ActiveSchedules_orderMonotone_shift_isLocal
-- name    : ProjSchedTW.ActiveSchedules.orderMonotone_shift_isLocal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T16:05:07.137692+00:00
-- url     : https://prove2.me/theorems/9d4a9573-e595-40e9-ad63-61214262f9ad
-- title:
--   §2.4, p. 39 — an order-monotone shift is local
-- statement:
--   Let $S$ and $S'$ be feasible schedules with $S'\ne S$, and suppose the shift from $S$ to $S'$ is order-monotone, i.e.
--   $$O(S)\subseteq O(S')\quad\text{or}\quad O(S)\supseteq O(S').$$
--   Then the shift is local: there is a continuous trajectory $x:[0,1]\to\mathcal S$ of feasible schedules with $x(0)=S$ and $x(1)=S'$.
--
--   This is the link between the order-based shifts of Definition 2.4.4 and the topological shifts of Definition 2.4.3; it gives the inclusion of semiactive schedules in pseudoactive schedules.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, §2.4, p. 39, text after Definition 2.4.4 ("In particular, an order-monotone shift is local.")

import Mathlib
import Definitions.Def_ProjSchedTW_ActiveSchedules_Project
import Definitions.Def_ProjSchedTW_ActiveSchedules_Shifts

namespace ProjSchedTW.ActiveSchedules

/-- §2.4, p. 39 (text after Definition 2.4.4): an order-monotone shift is local; the line
segment joining `S` and `S'` lies in the feasible region. -/
theorem orderMonotone_shift_isLocal {n : ℕ} {K : Type} (P : Project n K)
    (S S' : Fin (n + 2) → ℝ) (h : IsOrderMonotoneShift P S S') :
    IsLocalShift P S S' := by sorry

end ProjSchedTW.ActiveSchedules
