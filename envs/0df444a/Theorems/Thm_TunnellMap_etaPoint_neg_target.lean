-- Prove2me | Theorems.Thm_TunnellMap_etaPoint_neg_target
-- name    : TunnellMap.etaPoint_neg_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:09:41.627875+00:00
-- url     : https://prove2.me/theorems/ee661ec9-0f35-4f33-a9d6-8e93e7d1d987
-- title:
--   Tunnell Map: eta Point neg target
-- statement:
--   The Tunnell Map construction uses the eta Point neg target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L352-L361
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L352-L361

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.etaPoint_neg_target {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPoint s (negAResidual t) = - etaPoint s t := by sorry
