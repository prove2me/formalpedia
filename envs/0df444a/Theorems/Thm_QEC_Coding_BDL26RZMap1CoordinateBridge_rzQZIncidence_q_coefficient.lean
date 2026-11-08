-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RZMap1CoordinateBridge_rzQZIncidence_q_coefficient
-- name    : QEC.Coding.BDL26RZMap1CoordinateBridge.rzQZIncidence_q_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:17:47.590128+00:00
-- url     : https://prove2.me/theorems/d4ca0ef9-55db-45a6-93dd-d9fa35482b12
-- title:
--   BDL26 RZMap1 Coordinate Bridge: rz QZIncidence q coefficient
-- statement:
--   A shifted Q vertex contributes once to each adjacent actual Z block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1443-L1455
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZCoordinateBridge.lean#L1443-L1455

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

theorem QEC.Coding.BDL26RZMap1CoordinateBridge.rzQZIncidence_q_coefficient
    (P : TannerSquarePresentation) (A : TannerSquareAdmissible P)
    (S : OddScale) (q : P.Q) (z : P.Z)
    (qVertex : QDoubleCylinderVertex (transposePresentation P) q S)
    (zVertex : ZDoubleCylinderVertex P z S) :
    (if rzQZIncidence P A S (Sum.inr ⟨q, qVertex⟩) ⟨z, zVertex⟩ = true
      then (1 : Field) else 0) =
      if hqz : P.qz q z = true then
        vertexIndicator (qToZDoubleCylinderVertex P A q z hqz S qVertex) zVertex
      else 0 := by sorry
