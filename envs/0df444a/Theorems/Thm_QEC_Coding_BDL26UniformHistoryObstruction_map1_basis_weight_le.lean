-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_map1_basis_weight_le
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.map1_basis_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:31:48.929873+00:00
-- url     : https://prove2.me/theorems/50d86c6c-9bd3-4903-9a01-bd85f985fddb
-- title:
--   BDL26 Uniform History Obstruction: map1 basis weight le
-- statement:
--   Each actual incident Z block contributes at most one half-scale path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L122-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformWeight.lean#L122-L142

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26XLocalRadialParity BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.map1_basis_weight_le (P : TannerSquarePresentation)
    (A : TannerSquareAdmissibleV4 P) (S : OddScale) (q : P.Q) :
    HammingWeight (map1Coord P A S (canonicalBasisWord q)) ≤
      1 + qZDegree P q * S.half := by sorry
