-- Prove2me | Theorems.Thm_PigeonholeDesign_Upper_assign_balanced
-- name    : PigeonholeDesign.Upper.assign_balanced
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:11.75691+00:00
-- url     : https://prove2.me/theorems/da953207-91a6-4700-83b8-a8c3cd314560
-- title:
--   p. 16, after Definition 3 — every run of a pigeonhole design puts T/2 subjects in each group
-- statement:
--   Let $T$ be even. For every partition of the covariate space into pigeonholes, every arrival sequence $x$, and every realization of the fair coins, the pigeonhole design assigns exactly $T/2$ subjects to the control group and exactly $T/2$ subjects to the treated group:
--   $$|A|=|B|=\frac T2 .$$
--
--   This is the role of Step 1 of Definition 3. It guarantees that the discrepancy $d_{A,B}$ of every run is a genuine perfect matching between groups of equal size.
--
--   **Formalization Note** The statement holds for an arbitrary covariate type and an arbitrary labelling of pigeonholes. It is the guard against the junk value $0$ that the formal discrepancy takes on unbalanced splits: it shows that the designs never produce one.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. 16, remark following Definition 3

import Mathlib
import Definitions.Def_PigeonholeDesign_Upper_Setting

namespace PigeonholeDesign.Upper

theorem assign_balanced {E ι : Type*} [DecidableEq ι] {T : ℕ} (hT : Even T)
    (hole : E → ι) (x : Fin T → E) (coin : Fin T → Bool) :
    (Finset.univ.filter (fun t => assign hole x coin t = false)).card = T / 2 ∧
    (Finset.univ.filter (fun t => assign hole x coin t = true)).card = T / 2 := by sorry

end PigeonholeDesign.Upper
