-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_map1Coord_delta1_canonicalBasis
-- name    : QEC.Coding.BDL26RZMap1CoordinateBridge.map1Coord_delta1_canonicalBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:18:33.175972+00:00
-- url     : https://prove2.me/theorems/0855f819-2756-42aa-879e-3cf7c1f8826c
-- title:
--   BDL26 RZMap1 Coordinate Bridge: map1 Coord delta1 canonical Basis
-- statement:
--   Canonical-basis degree-one equation for the concrete RZ map.  This is the
--   RZ map1/map2 commutation row consumed by the downstream full-map assembler.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1596-L1708
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1596-L1708

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

theorem QEC.Coding.BDL26RZMap1CoordinateBridge.map1Coord_delta1_canonicalBasis
    (P : TannerSquarePresentation) (A4 : TannerSquareAdmissibleV4 P)
    (S : OddScale) (q : P.Q) :
    tannerCoboundary1
        (rzReplacementPresentation P A4.toTannerSquareAdmissible S)
        (map1Coord P A4 S (canonicalBasisWord q)) =
      map2Coord P A4 S
        (tannerCoboundary1 P (canonicalBasisWord q)) := by sorry
