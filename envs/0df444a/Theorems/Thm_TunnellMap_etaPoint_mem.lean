-- Prove2me | Theorems.Thm_TunnellMap_etaPoint_mem
-- name    : TunnellMap.etaPoint_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:05:09.97552+00:00
-- url     : https://prove2.me/theorems/2cd0c196-7525-4727-b26c-76a564dbc88b
-- title:
--   Tunnell Map: eta Point mem
-- statement:
--   The Tunnell Map construction uses the eta Point mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L339-L343
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L339-L343

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.etaPoint_mem {n : ℤ} (s : BResidual n) (t : AResidual n) :
    etaPoint s t = 1 ∨ etaPoint s t = -1 := by sorry
