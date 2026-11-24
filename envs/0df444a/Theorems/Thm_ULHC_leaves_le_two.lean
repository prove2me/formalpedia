-- Prove2me | Theorems.Thm_ULHC_leaves_le_two
-- name    : ULHC.leaves_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:52:33.340801+00:00
-- url     : https://prove2.me/theorems/56ba07fc-ca91-4816-8910-7853ec4d1c1f
-- title:
--   ULHC: leaves le two
-- statement:
--   The ULHC construction uses the leaves le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L452-L567
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Graph.lean#L452-L567

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.leaves_le_two {V : Finset Pt} :
    ∀ (n : ℕ) (F : Finset Edge), F.card = n → Inside V F → (∀ y, deg F y ≤ 2) →
      ∀ x, (V.filter (fun y => Conn F x y ∧ deg F y = 1)).card ≤ 2 := by sorry
