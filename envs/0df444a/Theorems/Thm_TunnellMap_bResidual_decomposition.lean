-- Prove2me | Theorems.Thm_TunnellMap_bResidual_decomposition
-- name    : TunnellMap.bResidual_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:11:33.885813+00:00
-- url     : https://prove2.me/theorems/b86de2d9-92df-4a8b-87d5-2a95cc11a1ee
-- title:
--   Tunnell Map: b Residual decomposition
-- statement:
--   The Tunnell Map construction uses the b Residual decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L240-L244
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L240-L244

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.bResidual_decomposition (x : BResidual n) :
    signActB (bResidualSign x)
        (canonicalBResidualRepresentative ((bResidualInvolution n).orbit x)) = x := by sorry
