-- Prove2me | Theorems.Thm_ULHC_nbA_ne
-- name    : ULHC.nbA_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:00:35.766867+00:00
-- url     : https://prove2.me/theorems/19fb215d-095b-4892-a413-39f98a2c9a32
-- title:
--   ULHC: nb A ne
-- statement:
--   The ULHC construction uses the nb A ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L64-L65
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Complete.lean#L64-L65

import Definitions.Def_ULHC_Reverse
import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.nbA_ne (d : Pt) (s : Side) : nb d (latA s) ≠ d := by sorry
