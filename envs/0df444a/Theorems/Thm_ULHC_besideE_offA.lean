-- Prove2me | Theorems.Thm_ULHC_besideE_offA
-- name    : ULHC.besideE_offA
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:07:28.271442+00:00
-- url     : https://prove2.me/theorems/1f214ca7-b067-45c9-8d12-8f2115729413
-- title:
--   ULHC: beside E off A
-- statement:
--   The ULHC construction uses the beside E off A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L310-L315
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/PathComplete.lean#L310-L315

import Definitions.Def_ULHC_NearCA
import Definitions.Def_ULHC_LinkGraph
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_PathComplete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.besideE_offA (c : Pt) (d : Side) (k : ℕ) {j : ℕ} (hj : 1 ≤ j) {y : Edge}
    (hy : y ∈ cellE (cellJ (nb (cellJ c d (k + 1)) (latA d)) d j)) :
    ∀ i ≤ k + 1, y ∉ cellE (cellJ c d i) := by sorry
