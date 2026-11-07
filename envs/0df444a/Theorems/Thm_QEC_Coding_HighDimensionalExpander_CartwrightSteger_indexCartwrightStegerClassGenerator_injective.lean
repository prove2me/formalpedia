-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerClassGenerator_injective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerClassGenerator_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:47:56.770125+00:00
-- url     : https://prove2.me/theorems/c7d176df-a99e-4463-bf32-13de34c9cf2a
-- title:
--   Cartwright Steger: index Cartwright Steger Class Generator injective
-- statement:
--   The source projective constant classes index distinct finite
--   Cartwright--Steger generators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L527-L535
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L527-L535

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCartwrightStegerClassGenerator_injective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective
      (indexCartwrightStegerClassGenerator P r level) := by sorry
