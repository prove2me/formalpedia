-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_signOf_mem
-- name    : TunnellMap.FreeInvolution.signOf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:04:41.069025+00:00
-- url     : https://prove2.me/theorems/a7ce339d-9e98-5ad3-b742-0cc673ac5726
-- title:
--   Free Involution: sign Of mem
-- statement:
--   The Free Involution construction uses the sign Of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L83-L87
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L83-L87

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)
variable {K : Type*} [LinearOrder K]

theorem TunnellMap.FreeInvolution.signOf_mem (key : X → K) (x : X) :
    I.signOf key x = 1 ∨ I.signOf key x = -1 := by sorry
