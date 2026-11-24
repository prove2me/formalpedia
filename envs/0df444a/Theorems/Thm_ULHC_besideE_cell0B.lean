-- Prove2me | Theorems.Thm_ULHC_besideE_cell0B
-- name    : ULHC.besideE_cell0B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:08:12.840448+00:00
-- url     : https://prove2.me/theorems/18d78454-8af7-461b-b459-33361e8d963c
-- title:
--   ULHC: beside E cell0 B
-- statement:
--   The ULHC construction uses the beside E cell0 B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L333-L340
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L333-L340

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.besideE_cell0B (c : Pt) (d : Side) (k : ℕ) {y : Edge}
    (hy : y ∈ cellE (nb (cellJ c d (k + 1)) (latB d))) (hne : y ≠ lat2 (cellJ c d (k + 1)) d) :
    ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) := by sorry
