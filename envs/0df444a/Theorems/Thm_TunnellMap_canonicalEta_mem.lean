-- Prove2me | Theorems.Thm_TunnellMap_canonicalEta_mem
-- name    : TunnellMap.canonicalEta_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:11:14.540802+00:00
-- url     : https://prove2.me/theorems/69d06e7d-cb5c-5e34-ae9f-63d7da64d89c
-- title:
--   Tunnell Map: canonical Eta mem
-- statement:
--   The Tunnell Map construction uses the canonical Eta mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L399-L403
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L399-L403

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.canonicalEta_mem {n : ℤ} (hnpos : 0 < n)
    (q : (bResidualInvolution n).Orbit)
    (o : (aResidualInvolution n hnpos).Orbit) :
    canonicalEta hnpos q o = 1 ∨ canonicalEta hnpos q o = -1 := by sorry
