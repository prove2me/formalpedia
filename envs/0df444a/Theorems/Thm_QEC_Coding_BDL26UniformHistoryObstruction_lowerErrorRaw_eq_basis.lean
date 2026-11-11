-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_lowerErrorRaw_eq_basis
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.lowerErrorRaw_eq_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:58:06.744599+00:00
-- url     : https://prove2.me/theorems/a9cac9bd-74f9-4bb9-833a-51f0ac4faa33
-- title:
--   BDL26 Uniform History Obstruction: lower Error Raw eq basis
-- statement:
--   The BDL26 Uniform History Obstruction construction uses the lower Error Raw eq basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L87-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L87-L99

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.lowerErrorRaw_eq_basis (S : OddScale) (n : Nat) :
    lowerErrorRaw S n = canonicalBasisWord (lowerBasisRaw S n) := by sorry
