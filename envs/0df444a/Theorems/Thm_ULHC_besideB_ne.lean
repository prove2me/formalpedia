-- Prove2me | Theorems.Thm_ULHC_besideB_ne
-- name    : ULHC.besideB_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:37:43.429+00:00
-- url     : https://prove2.me/theorems/c53debca-fdc4-4d7b-9534-f0c8f1efe06b
-- title:
--   ULHC: beside B ne
-- statement:
--   The ULHC construction uses the beside B ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L616-L618
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L616-L618

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.besideB_ne (c : Pt) (s : Side) (m j i : ℕ) :
    cellJ (nb (cellJ c s m) (latB s)) s j ≠ cellJ c s i := by sorry
