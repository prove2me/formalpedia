-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerError_eq_basis
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.lowerError_eq_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:58:14.014015+00:00
-- url     : https://prove2.me/theorems/60bba421-d631-472f-888f-f96aaabc31fc
-- title:
--   BDL26 Uniform History Obstruction: lower Error eq basis
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the lower Error eq basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L156-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L156-L161

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.lowerError_eq_basis (S : OddScale) (j : Nat) :
    lowerError S j = canonicalBasisWord (lowerBasis S j) := by sorry
