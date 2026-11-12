-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_actual_cx_boundary_z_zero
-- name    : QEC.Coding.BDL26UniformRXTail.actual_cx_boundary_z_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:12:40.319793+00:00
-- url     : https://prove2.me/theorems/754e9132-5900-49be-b165-c109a7df3de9
-- title:
--   BDL26 Uniform RXTail: actual cx boundary z zero
-- statement:
--   CX cleaning does not change either Z endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L300-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L300-L313

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.actual_cx_boundary_z_zero (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 2)).presentation.Z) (b : Fin 2) :
    (indexedFamily S (2 * j + 4)).coboundary1 (tailIndex j).succ
      (cxCorrectionTotal (tailData S j) (lowerSyndrome S j).val)
      ((tailData S j).induced.zPairEquiv (z,b)).val = 0 := by sorry
