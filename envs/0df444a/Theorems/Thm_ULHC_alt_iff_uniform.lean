-- Prove2me | Theorems.Thm_ULHC_alt_iff_uniform
-- name    : ULHC.alt_iff_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:31.649008+00:00
-- url     : https://prove2.me/theorems/e1c1ce85-8c44-4860-b971-3a90b3d4e486
-- title:
--   ULHC: alt iff uniform
-- statement:
--   The ULHC construction uses the alt iff uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L154-L172
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Arcs.lean#L154-L172

import Definitions.Def_ULHC_Potential
import Definitions.Def_ULHC_Arcs
set_option autoImplicit true
open ULHC

theorem ULHC.alt_iff_uniform (F : Finset Edge) (c : Pt) :
    Alt F c ↔ Source F c ∨ Sink F c := by sorry
