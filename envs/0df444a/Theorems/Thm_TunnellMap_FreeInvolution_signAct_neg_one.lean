-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_signAct_neg_one
-- name    : TunnellMap.FreeInvolution.signAct_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:02:56.571587+00:00
-- url     : https://prove2.me/theorems/171ebe6c-e342-5728-9532-a950dbee5c7f
-- title:
--   Free Involution: sign Act neg one
-- statement:
--   The Free Involution construction uses the sign Act neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L41-L42
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L41-L42

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)

theorem TunnellMap.FreeInvolution.signAct_neg_one (x : X) : I.signAct (-1) x = I.neg x := by sorry
