-- Prove2me | Theorems.Thm_TunnellMap_qForm_bLift
-- name    : TunnellMap.qForm_bLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:03.035057+00:00
-- url     : https://prove2.me/theorems/4a520c45-6de2-5e1e-94a0-bf3db000ff5f
-- title:
--   Tunnell Map: q Form b Lift
-- statement:
--   The Tunnell Map construction uses the q Form b Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L23-L27
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L23-L27

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.qForm_bLift {n : ℤ} (p : BOddRep n) : qForm (bLift p) = n := by sorry
