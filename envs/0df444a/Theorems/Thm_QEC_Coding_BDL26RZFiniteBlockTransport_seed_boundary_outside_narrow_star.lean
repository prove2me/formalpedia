-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZFiniteBlockTransport_seed_boundary_outside_narrow_star
-- name    : QEC.Coding.BDL26RZFiniteBlockTransport.seed_boundary_outside_narrow_star
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:19:22.204938+00:00
-- url     : https://prove2.me/theorems/d3515c7e-0ffb-4360-92a1-f7653953b8eb
-- title:
--   BDL26 RZFinite Block Transport: seed boundary outside narrow star
-- statement:
--   This is a constructor-boundary witness, not a canonical two-run counterexample.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L1035-L1110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZFiniteBlockTransport.lean#L1035-L1110

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZErrorPullback
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RZFiniteBlockTransport
open BDL26FiniteAlternatingCore
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge BDL26ReplacementSupport
open BDL26ReplacementCochainMaps BDL26LevelTwoDistance BDL26IndexedDecoder
open MultiscaleDecoder RZCoarseGraining RZCoarseGrainingData
open scoped BigOperators Classical
open BDL26RZDecoderAdapter BDL26RZErrorPullback
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val % 2=0)

theorem QEC.Coding.BDL26RZFiniteBlockTransport.seed_boundary_outside_narrow_star (S : OddScale) :
    rzCoboundary0 baseTannerSquarePresentation baseTannerSquareAdmissibleV4 S
      (canonicalBasisWord (rzMap1QEdgeX baseTannerSquarePresentation S (4 : BaseQubit) (seedQEdge S)))
      (seedOutsideCoordinate S)=1 ∧
    seedOutsideCoordinate S ∉ Coordinates.inputBlocks baseTannerSquarePresentation S
      (Finset.univ.filter fun q => baseTannerSquarePresentation.qz q (0 : BaseZ)=true) {(0 : BaseZ)} := by sorry
