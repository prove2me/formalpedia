-- Prove2me | Theorems.Thm_TunnellMap_etaPoint_eq_one_iff
-- name    : TunnellMap.etaPoint_eq_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:12:19.451865+00:00
-- url     : https://prove2.me/theorems/d7e41742-093c-46c8-b7c8-8a295eb34006
-- title:
--   Tunnell Map: eta Point eq one iff
-- statement:
--   The Tunnell Map construction uses the eta Point eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L345-L350
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L345-L350

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.etaPoint_eq_one_iff {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPoint s t = 1 ↔
      directionKey (plusVector s t) < directionKey (minusVector s t) := by sorry
