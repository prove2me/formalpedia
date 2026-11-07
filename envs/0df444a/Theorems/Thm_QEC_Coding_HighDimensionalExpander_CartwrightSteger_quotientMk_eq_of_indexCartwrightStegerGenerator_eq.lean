-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_quotientMk_eq_of_indexCartwrightStegerGenerator_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.quotientMk_eq_of_indexCartwrightStegerGenerator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:48:05.65282+00:00
-- url     : https://prove2.me/theorems/1e09c49f-1421-46bf-a973-3523611d7914
-- title:
--   Cartwright Steger: quotient Mk eq of index Cartwright Steger Generator eq
-- statement:
--   Equality of two projective generators forces their constant parameters
--   to differ by a base-field scalar.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L363-L461
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L363-L461

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.quotientMk_eq_of_indexCartwrightStegerGenerator_eq
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : (ConstantExtension P r)ˣ)
    (hprojective : indexCartwrightStegerGenerator P r level u =
      indexCartwrightStegerGenerator P r level v) :
    (QuotientGroup.mk u : ConstantProjectiveClass P r) =
      QuotientGroup.mk v := by sorry
