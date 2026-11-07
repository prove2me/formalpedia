-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerClassGenerator_ne_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerClassGenerator_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:48:15.576197+00:00
-- url     : https://prove2.me/theorems/1c76c269-2ce1-403c-976e-fa5d9b6a9b9d
-- title:
--   Cartwright Steger: index Cartwright Steger Class Generator ne one
-- statement:
--   No finite Cartwright--Steger generator collapses to the identity.
--   All source-indexed generators are conjugates of the same element `b`; if
--   one conjugate were trivial, every conjugate would be trivial, contradicting
--   the proved injectivity of the source projective indexing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L570-L593
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L570-L593

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerClassGenerator_ne_one
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    indexCartwrightStegerClassGenerator P r level u ≠ 1 := by sorry
