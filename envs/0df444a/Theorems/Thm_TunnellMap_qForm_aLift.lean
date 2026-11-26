-- Prove2me | Theorems.Thm_TunnellMap_qForm_aLift
-- name    : TunnellMap.qForm_aLift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:11.276815+00:00
-- url     : https://prove2.me/theorems/1007b299-29c0-5ffe-87b5-578f09bd06d6
-- title:
--   Tunnell Map: q Form a Lift
-- statement:
--   The Tunnell Map construction uses the q Form a Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L29-L33
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L29-L33

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.qForm_aLift {n : ℤ} (p : ARep n) : qForm (aLift p) = n := by sorry
