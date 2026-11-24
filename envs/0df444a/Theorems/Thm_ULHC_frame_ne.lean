-- Prove2me | Theorems.Thm_ULHC_frame_ne
-- name    : ULHC.frame_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:19:04.463308+00:00
-- url     : https://prove2.me/theorems/9bfc8ae4-6766-4311-8d48-e437a81f65de
-- title:
--   ULHC: frame ne
-- statement:
--   The ULHC construction uses the frame ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L61-L64
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/ChainLinks.lean#L61-L64

import Definitions.Def_ULHC_NearLemma
import Definitions.Def_ULHC_ChainLinks
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.frame_ne (d : Pt) (tf : Side) : back d tf ≠ lat1 d tf ∧ back d tf ≠ lat2 d tf ∧
    front d tf ≠ lat1 d tf ∧ front d tf ≠ lat2 d tf ∧ lat1 d tf ≠ lat2 d tf ∧ back d tf ≠ front d tf := by sorry
