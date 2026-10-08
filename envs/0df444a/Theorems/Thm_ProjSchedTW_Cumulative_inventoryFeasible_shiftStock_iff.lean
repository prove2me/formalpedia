-- Prove2me | Theorems.Thm_ProjSchedTW_Cumulative_inventoryFeasible_shiftStock_iff
-- name    : ProjSchedTW.Cumulative.inventoryFeasible_shiftStock_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T00:01:20.30601+00:00
-- url     : https://prove2.me/theorems/dcfec505-4d13-4f83-b254-241a9ee95a01
-- title:
--   §2.12.1, p. 131 — adding a_k to initial stock, safety stock and capacity gives an equivalent instance
-- statement:
--   Consider a project with discrete cumulative resources as in §2.12.1 and integers $(a_k)_{k\in\mathcal R^\gamma}$. Form the shifted instance by replacing the initial stock $r_{0k}$ with $r_{0k}+a_k$, the safety stock $\underline R_k$ with $\underline R_k+a_k$ and the storage capacity $\overline R_k$ with $\overline R_k+a_k$, for every resource $k$. Then for every schedule $S$ (so $S_0=0$ and $S_i\ge 0$),
--   $$
--   S \text{ is inventory-feasible for the shifted instance} \iff S \text{ is inventory-feasible for the original instance.}
--   $$
--
--   This is the book's justification that the convention of Remark 2.12.2 ($\underline R_k\le 0\le\overline R_k$) is no loss of generality: temporal constraints are untouched by the shift, so both instances have the same feasible schedules.
--
--   **Formalization Note** "Equivalent instance" is expressed as equality of the sets of inventory-feasible schedules; the time-lag constraints are not part of this mission's model and are unchanged by the shift. Inventory-feasibility is required for all $t\ge 0$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 131, paragraph after Remark 2.12.2 (invariance under adding a_k to r_0k, safety stock and storage capacity)

import Mathlib
import Definitions.Def_ProjSchedTW_Cumulative_Model

namespace ProjSchedTW.Cumulative

/-- §2.12.1, p. 131, after Remark 2.12.2: adding the same integer `a_k` to the initial inventory,
the safety stock and the storage capacity yields an equivalent instance. -/
theorem inventoryFeasible_shiftStock_iff {n : ℕ} {K : Type} (P : CumulativeProject n K)
    (a : K → ℤ) (S : Fin (n + 2) → ℝ) (hS : IsSchedule S) :
    InventoryFeasible (shiftStock P a) S ↔ InventoryFeasible P S := by sorry

end ProjSchedTW.Cumulative
