-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map1BasisImage_support_eq_parentRegion
-- name    : QEC.Coding.BDL26RZMap1CoordinateBridge.map1BasisImage_support_eq_parentRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:18:33.792704+00:00
-- url     : https://prove2.me/theorems/4d73bf5c-8e43-41ad-914f-b3d1c7e5de1b
-- title:
--   BDL26 RZMap1 Coordinate Bridge: map1 Basis Image support eq parent Region
-- statement:
--   Exact F10 parent-support identity for every old-Q basis coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L936-L944
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L936-L944

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZLocalReplacement
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCoordinateBridge
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26RZMap1CoordinateBridge
open scoped BigOperators
open BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity
open BDL26RZLocalReplacement
open MultiscaleDecoder
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.rzQDecidableEq
attribute [local instance] rzQFintype
attribute [local instance] QEC.Coding.BDL26RZMap1CoordinateBridge.subdivisionEdgeDecidableEq
attribute [local instance] subdivisionEdgeDecidableEq
universe u

theorem QEC.Coding.BDL26RZMap1CoordinateBridge.map1BasisImage_support_eq_parentRegion
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) :
    hammingSupport (map1BasisImage P A4 S q) =
      rzMap1ParentRegion P A4 S q := by sorry
