-- Prove2me | Theorems.Thm_ULHC_besideA_ne
-- name    : ULHC.besideA_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:37:47.10642+00:00
-- url     : https://prove2.me/theorems/93cef283-02c4-46f5-9c0f-32330c370846
-- title:
--   ULHC: beside A ne
-- statement:
--   The ULHC construction uses the beside A ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L612-L614
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L612-L614

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.besideA_ne (c : Pt) (s : Side) (m j i : ℕ) :
    cellJ (nb (cellJ c s m) (latA s)) s j ≠ cellJ c s i := by sorry
