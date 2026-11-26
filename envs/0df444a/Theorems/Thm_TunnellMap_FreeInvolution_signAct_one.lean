-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_signAct_one
-- name    : TunnellMap.FreeInvolution.signAct_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:03:09.924801+00:00
-- url     : https://prove2.me/theorems/3a12e618-c8ab-474d-9f26-07add67ce654
-- title:
--   Free Involution: sign Act one
-- statement:
--   The Free Involution construction uses the sign Act one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L39-L39
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L39-L39

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X : Type*} (I : FreeInvolution X)

theorem TunnellMap.FreeInvolution.signAct_one (x : X) : I.signAct 1 x = x := by sorry
