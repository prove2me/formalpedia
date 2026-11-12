-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformRXTail_lower_syndrome_z_zero
-- name    : QEC.Coding.BDL26UniformRXTail.lower_syndrome_z_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:14:21.217321+00:00
-- url     : https://prove2.me/theorems/292ac872-9026-488e-b483-5b9bb52c877d
-- title:
--   BDL26 Uniform RXTail: lower syndrome z zero
-- statement:
--   The fixed radial input has no Z endpoint syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L293-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformRXTail/Normalization.lean#L293-L297

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Normalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformRXTail
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26RXDecoderAdapter BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical BigOperators
open BDL26DecodingGraph BDL26IndexedDecoder BDL26UniformHistoryObstruction RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData

theorem QEC.Coding.BDL26UniformRXTail.lower_syndrome_z_zero (S : OddScale) (j : Nat)
    (z : (state S (2 * j + 2)).presentation.Z) (b : Fin 2) :
    (lowerSyndrome S j).val ((tailData S j).induced.zPairEquiv (z,b)).val = 0 := by sorry
