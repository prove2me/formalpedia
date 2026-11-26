-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_orbit_signAct
-- name    : TunnellMap.FreeInvolution.orbit_signAct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:03:50.99659+00:00
-- url     : https://prove2.me/theorems/d1ffde2c-f6d6-420a-a7b9-42fa88ddf465
-- title:
--   Free Involution: orbit sign Act
-- statement:
--   The Free Involution construction uses the orbit sign Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L57-L62
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L57-L62

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)

theorem TunnellMap.FreeInvolution.orbit_signAct (σ : ℤ) (x : X) :
    I.orbit (I.signAct σ x) = I.orbit x := by sorry
