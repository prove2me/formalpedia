-- Prove2me | Theorems.Thm_ULHC_besideA_not_mid
-- name    : ULHC.besideA_not_mid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:38:03.55699+00:00
-- url     : https://prove2.me/theorems/49becf33-6272-4728-a0b7-144eb622f67b
-- title:
--   ULHC: beside A not mid
-- statement:
--   The ULHC construction uses the beside A not mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L620-L625
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/NearCA.lean#L620-L625

import Definitions.Def_ULHC_ChainLinks
import Definitions.Def_ULHC_Complete
import Definitions.Def_ULHC_NearCA
set_option autoImplicit true
open ULHC
open Finset

theorem ULHC.besideA_not_mid (c : Pt) (s : Side) (k : ℕ) {tf : Side} (ht : tf = s ∨ tf = s.opp) :
    ¬ IsMid c s k (back1 (nb (cellJ c s (k + 1)) (latA s)) tf) ∧
      ¬ IsMid c s k (front1 (nb (cellJ c s (k + 1)) (latA s)) tf) := by sorry
