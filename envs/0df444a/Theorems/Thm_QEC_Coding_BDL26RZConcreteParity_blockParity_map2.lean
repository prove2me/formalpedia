-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZConcreteParity_blockParity_map2
-- name    : QEC.Coding.BDL26RZConcreteParity.blockParity_map2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:25:34.548011+00:00
-- url     : https://prove2.me/theorems/8e030407-1575-4992-a629-93978f9547a1
-- title:
--   BDL26 RZConcrete Parity: block Parity map2
-- statement:
--   Block parity is a left inverse of the actual RZ degree-two map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L77-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZConcreteParity.lean#L77-L87

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZConcreteParity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RZConcreteParity
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped BigOperators Classical

theorem QEC.Coding.BDL26RZConcreteParity.blockParity_map2 (P : TannerSquarePresentation) (A : TannerSquareAdmissibleV4 P)
    (S : OddScale) (s : Word BDL26Field P.Z) :
    blockParity P S (map2Coord P A S s) = s := by sorry
