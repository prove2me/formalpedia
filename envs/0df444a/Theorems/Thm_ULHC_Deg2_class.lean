-- Prove2me | Theorems.Thm_ULHC_Deg2_class
-- name    : ULHC.Deg2.class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:24:23.39014+00:00
-- url     : https://prove2.me/theorems/b45af1e4-46b6-4c81-b9ab-e1501dabf451
-- title:
--   Deg2: class
-- statement:
--   The Deg2 construction uses the class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L432-L433
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/StripCount.lean#L432-L433

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.Deg2.class {V : Finset Pt} {F : Finset Edge} (h : Deg2 V F) {a : Pt} (ha : a ∈ V) {z : Pt}
    (hz : Conn F a z) : deg F z = 2 := by sorry
