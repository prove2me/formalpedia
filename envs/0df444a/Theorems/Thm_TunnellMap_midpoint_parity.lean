-- Prove2me | Theorems.Thm_TunnellMap_midpoint_parity
-- name    : TunnellMap.midpoint_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:29.429312+00:00
-- url     : https://prove2.me/theorems/de935e94-fd19-51ea-9d6d-4fb19551fa30
-- title:
--   Tunnell Map: midpoint parity
-- statement:
--   Lemma 2.2: both lifted midpoint halves are integral and have odd third
--   coordinate.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L101-L142
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L101-L142

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.midpoint_parity {n : ℤ} (hn : Odd n) (s : BOddRep n) (t : ARep n) :
    ∃ hPlus hMinus : Triple,
      IsHalfSum hPlus (bLift s) (aLift t) ∧ Odd hPlus.z ∧
      IsHalfDiff hMinus (bLift s) (aLift t) ∧ Odd hMinus.z := by sorry
