-- Prove2me | Theorems.Thm_TunnellMap_etaPoint_neg_source
-- name    : TunnellMap.etaPoint_neg_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:09:36.221803+00:00
-- url     : https://prove2.me/theorems/2720e4e0-caed-5260-8889-1575bc77ba48
-- title:
--   Tunnell Map: eta Point neg source
-- statement:
--   The Tunnell Map construction uses the eta Point neg source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L363-L374
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L363-L374

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.etaPoint_neg_source {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPoint (negBResidual s) t = - etaPoint s t := by sorry
