-- Prove2me | Theorems.Thm_TunnellMap_FreeInvolution_liftOrbitEquiv_representative
-- name    : TunnellMap.FreeInvolution.liftOrbitEquiv_representative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:40.289402+00:00
-- url     : https://prove2.me/theorems/487eb4f5-e44b-594e-9323-bea14f61249b
-- title:
--   Free Involution: lift Orbit Equiv representative
-- statement:
--   The Free Involution construction uses the lift Orbit Equiv representative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitLift.lean#L44-L50
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/OrbitLift.lean#L44-L50

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_Assembly
import Definitions.Def_TunnellMap_OrbitLift
set_option autoImplicit true
open TunnellMap
open TunnellMap.FreeInvolution
variable {X Y : Type*} (I : FreeInvolution X) (J : FreeInvolution Y)
variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
omit [Fintype X] [Fintype Y]

theorem TunnellMap.FreeInvolution.liftOrbitEquiv_representative (M : I.Orbit ≃ J.Orbit)
    (sign : ∀ _q : I.Orbit, Bool ≃ Bool) (q : I.Orbit) :
    I.liftOrbitEquiv J M sign (I.representative q) =
      if sign q false then J.neg (J.representative (M q))
      else J.representative (M q) := by sorry
