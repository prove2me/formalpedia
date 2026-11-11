-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_basis_coboundary_weight
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.basis_coboundary_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:00:46.386801+00:00
-- url     : https://prove2.me/theorems/6e44e244-8a46-49b8-9062-ab30d4248043
-- title:
--   BDL26 Uniform History Obstruction: basis coboundary weight
-- statement:
--   This is a global column degree, including every Z neighbour.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L27-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L27-L31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.basis_coboundary_weight (P : TannerSquarePresentation) (q : P.Q) :
    HammingWeight (tannerCoboundary1 P (canonicalBasisWord q)) = qZDegree P q := by sorry
