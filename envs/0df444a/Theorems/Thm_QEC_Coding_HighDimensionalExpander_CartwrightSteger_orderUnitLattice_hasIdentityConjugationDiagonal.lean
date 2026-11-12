-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderUnitLattice_hasIdentityConjugationDiagonal
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitLattice_hasIdentityConjugationDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:46:46.639679+00:00
-- url     : https://prove2.me/theorems/04c5f526-aa87-4751-afe3-336712881c75
-- title:
--   Cartwright Steger: order Unit Lattice has Identity Conjugation Diagonal
-- statement:
--   A compact building image of an arithmetic lattice unit satisfies the
--   identity-diagonal condition at infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L190-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/SimpleTransitivity.lean#L190-L219

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderUnitLattice_hasIdentityConjugationDiagonal
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ)
    (hu : u ∈ CartwrightStegerOrderUnitLattice P r)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank) :
    BuildingElementHasIdentityConjugationDiagonal P r
      (orderUnitToBuildingPGL P r u) := by sorry
