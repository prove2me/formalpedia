-- Prove2me | Theorems.Thm_ULHC_along_not_mid
-- name    : ULHC.along_not_mid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T04:04:00.360056+00:00
-- url     : https://prove2.me/theorems/a92dd2b8-280a-4751-96c7-2c79ac4f70c8
-- title:
--   ULHC: along not mid
-- statement:
--   The ULHC construction uses the along not mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L714-L718
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L714-L718

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.along_not_mid (c : Pt) (s : Side) (k : ℕ) :
    ¬ IsMid c s k (back1 (cellJ c s (k + 3)) s) ∧ ¬ IsMid c s k (front1 (cellJ c s (k + 3)) s) := by sorry
