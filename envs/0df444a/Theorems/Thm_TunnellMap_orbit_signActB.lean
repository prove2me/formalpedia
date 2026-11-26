-- Prove2me | Theorems.Thm_TunnellMap_orbit_signActB
-- name    : TunnellMap.orbit_signActB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:04:21.128507+00:00
-- url     : https://prove2.me/theorems/71784afd-0035-458d-90b2-2d73e231f4a2
-- title:
--   Tunnell Map: orbit sign Act B
-- statement:
--   The Tunnell Map construction uses the orbit sign Act B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L266-L269
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L266-L269

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.orbit_signActB (σ : ℤ) (x : BResidual n) :
    (bResidualInvolution n).orbit (signActB σ x) =
      (bResidualInvolution n).orbit x := by sorry
