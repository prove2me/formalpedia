-- Prove2me | Theorems.Thm_ULHC_column
-- name    : ULHC.column
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:49:18.683154+00:00
-- url     : https://prove2.me/theorems/bdeb3a0c-2fe1-40bb-bf69-ca60b845cef3
-- title:
--   ULHC: column
-- statement:
--   The ULHC construction uses the column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase2.lean#L200-L264
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Phase2.lean#L200-L264

import Definitions.Def_ULHC_Phase
import Definitions.Def_ULHC_Phase2
set_option autoImplicit true
open ULHC
open Finset Classical
variable {V : Finset Pt} {F H : Finset Edge} {P : Finset Pt}
  (hF : Deg2 V F) (hH : Deg2 V H) (hs : Solid V) (hB : Border V F P)
include hF hH hs

theorem ULHC.column {w : Pt} {s : Side} {o : Bool} (hp : ParOK w s o)
    (_hb : back w s ∈ F) (hl1 : lat1 w s ∉ F) (hl2 : lat2 w s ∉ F) (hg : Good o (D F H w)) :
    ∀ J, (∀ j < J, front (cellJ w s j) s ∈ F ↔ j % 2 = 1) →
      (∀ j ≤ J, (lat1 (cellJ w s j) s ∈ F ↔ j % 2 = 1) ∧
        (lat2 (cellJ w s j) s ∈ F ↔ j % 2 = 1)) ∧
      ∀ j ≤ J, Good o (D F H (cellJ w s j)) := by sorry
