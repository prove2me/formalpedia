-- Prove2me | Theorems.Thm_TunnellMap_vsmul_neg_one
-- name    : TunnellMap.vsmul_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:09:35.439713+00:00
-- url     : https://prove2.me/theorems/b8586012-6d89-4016-b1d1-2af489309342
-- title:
--   Tunnell Map: vsmul neg one
-- statement:
--   The Tunnell Map construction uses the vsmul neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L279-L280
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L279-L280

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.vsmul_neg_one (v : Triple) : vsmul (-1) v = negTriple v := by sorry
