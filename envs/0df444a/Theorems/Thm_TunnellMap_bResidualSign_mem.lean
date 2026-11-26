-- Prove2me | Theorems.Thm_TunnellMap_bResidualSign_mem
-- name    : TunnellMap.bResidualSign_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:10:34.682178+00:00
-- url     : https://prove2.me/theorems/f09a843b-c9b8-59a8-b59b-f90fd7c25cac
-- title:
--   Tunnell Map: b Residual Sign mem
-- statement:
--   The Tunnell Map construction uses the b Residual Sign mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L215-L217
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L215-L217

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.bResidualSign_mem (x : BResidual n) :
    bResidualSign x = 1 ∨ bResidualSign x = -1 := by sorry
