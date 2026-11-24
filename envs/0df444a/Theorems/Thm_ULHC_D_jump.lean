-- Prove2me | Theorems.Thm_ULHC_D_jump
-- name    : ULHC.D_jump
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:55.604581+00:00
-- url     : https://prove2.me/theorems/ef69bda1-f2b4-4997-a5a5-27a707659a7b
-- title:
--   ULHC: D jump
-- statement:
--   The ULHC construction uses the D jump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L102-L103
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/D.lean#L102-L103

import Definitions.Def_ULHC_Arcs
import Definitions.Def_ULHC_D
set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {d : Pt → ℕ} {F H : Finset Edge}
  (hF : IsFactor V d F) (hH : IsFactor V d H)
include hF hH

theorem ULHC.D_jump (e : Edge) : D F H e.hi - D F H e.lo = wD F H e := by sorry
