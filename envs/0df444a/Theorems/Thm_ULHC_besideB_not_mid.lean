-- Prove2me | Theorems.Thm_ULHC_besideB_not_mid
-- name    : ULHC.besideB_not_mid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:38:01.60184+00:00
-- url     : https://prove2.me/theorems/4c639139-f396-411f-9b9e-88a6e6cd0983
-- title:
--   ULHC: beside B not mid
-- statement:
--   The ULHC construction uses the beside B not mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L627-L632
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L627-L632

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.besideB_not_mid (c : Pt) (s : Side) (k : ℕ) {tf : Side} (ht : tf = s ∨ tf = s.opp) :
    ¬ IsMid c s k (back1 (nb (cellJ c s (k + 1)) (latB s)) tf) ∧
      ¬ IsMid c s k (front1 (nb (cellJ c s (k + 1)) (latB s)) tf) := by sorry
