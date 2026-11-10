-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_localResidual_map2_eq_zero
-- name    : QEC.Coding.BDL26RZConcreteParity.localResidual_map2_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:18:52.996736+00:00
-- url     : https://prove2.me/theorems/16bee583-30bf-4b8f-b63b-9403d4356c0e
-- title:
--   BDL26 RZConcrete Parity: local Residual map2 eq zero
-- statement:
--   The concrete residual vanishes; a chosen correction may still be a cycle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L113-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L113-L120

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RZConcreteParity.localResidual_map2_eq_zero (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (s : Word BDL26Field P.Z)
    (z : P.Z) :
    blockPart P S z (map2Coord P A S s) +
      rootLift P A S z (blockParity P S (map2Coord P A S s) z) = 0 := by sorry
