-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_basis_coboundary_support
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.basis_coboundary_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:32:20.571325+00:00
-- url     : https://prove2.me/theorems/24079d0a-c07e-45b3-98b9-4afa9f4375f7
-- title:
--   BDL26 Uniform History Obstruction: basis coboundary support
-- statement:
--   A binary basis error has precisely its incident Z checks as syndrome support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L17-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformReadoutWeight.lean#L17-L24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26BoundedValence BDL26TannerLocalRegularity
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26RZMap1CoordinateBridge
open BDL26OwnerParentObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26UniformHistoryObstruction.basis_coboundary_support (P : TannerSquarePresentation) (q : P.Q) :
    hammingSupport (tannerCoboundary1 P (canonicalBasisWord q)) =
      Finset.univ.filter (fun z => P.qz q z = true) := by sorry
