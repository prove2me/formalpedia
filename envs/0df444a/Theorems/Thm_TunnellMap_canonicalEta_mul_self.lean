-- Prove2me | Theorems.Thm_TunnellMap_canonicalEta_mul_self
-- name    : TunnellMap.canonicalEta_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:02:32.298009+00:00
-- url     : https://prove2.me/theorems/5fe5e7c4-6358-427e-ada6-5a7fbb30df06
-- title:
--   Tunnell Map: canonical Eta mul self
-- statement:
--   The Tunnell Map construction uses the canonical Eta mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L405-L409
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L405-L409

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.canonicalEta_mul_self {n : ℤ} (hnpos : 0 < n)
    (q : (bResidualInvolution n).Orbit)
    (o : (aResidualInvolution n hnpos).Orbit) :
    canonicalEta hnpos q o * canonicalEta hnpos q o = 1 := by sorry
