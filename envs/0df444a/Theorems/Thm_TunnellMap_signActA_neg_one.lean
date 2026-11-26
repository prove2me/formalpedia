-- Prove2me | Theorems.Thm_TunnellMap_signActA_neg_one
-- name    : TunnellMap.signActA_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:03:05.319115+00:00
-- url     : https://prove2.me/theorems/0d23eb68-6e16-527c-9f6c-d4fd27c164d9
-- title:
--   Tunnell Map: sign Act A neg one
-- statement:
--   The Tunnell Map construction uses the sign Act A neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L179-L181
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L179-L181

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.signActA_neg_one {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    signActA hnpos (-1) y = negAResidual y := by sorry
