-- Prove2me | Theorems.Thm_ULHC_besideE_offB
-- name    : ULHC.besideE_offB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:07:38.183153+00:00
-- url     : https://prove2.me/theorems/b0cd1226-bfa0-4b05-a12b-d18db8c5191f
-- title:
--   ULHC: beside E off B
-- statement:
--   The ULHC construction uses the beside E off B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L317-L322
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L317-L322

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.besideE_offB (c : Pt) (d : Side) (k : ℕ) {j : ℕ} (hj : 1 ≤ j) {y : Edge}
    (hy : y ∈ cellE (cellJ (nb (cellJ c d (k + 1)) (latB d)) d j)) :
    ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) := by sorry
