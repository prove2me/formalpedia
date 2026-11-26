-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_liftOrbitEquiv_neg_representative
-- name    : TunnellMap.FreeInvolution.liftOrbitEquiv_neg_representative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:13:45.442342+00:00
-- url     : https://prove2.me/theorems/5c441f17-1d18-5134-9f86-6e07660d5767
-- title:
--   Free Involution: lift Orbit Equiv neg representative
-- statement:
--   The value of the lifted equivalence at the antipode of a chosen source
--   representative.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L507-L514
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L507-L514

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
open TunnellMap.FreeInvolution
variable {X Y : Type*} (I : FreeInvolution X) (J : FreeInvolution Y)
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
omit [Fintype X] [Fintype Y]

theorem TunnellMap.FreeInvolution.liftOrbitEquiv_neg_representative (M : I.Orbit ≃ J.Orbit)
    (sign : ∀ _q : I.Orbit, Bool ≃ Bool) (q : I.Orbit) :
    I.liftOrbitEquiv J M sign (I.neg (I.representative q)) =
      if sign q true then J.neg (J.representative (M q))
      else J.representative (M q) := by sorry
