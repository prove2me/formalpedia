-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_indexColorQuotient
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_indexColorQuotient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:48:08.389562+00:00
-- url     : https://prove2.me/theorems/055c93e0-10f4-43ee-8136-cc740ccc55ae
-- title:
--   Cartwright Steger: nat Card index Color Quotient
-- statement:
--   Exact controlled index: the color-zero subgroup quotient is the full
--   projective determinant-class group.  The separate strong-approximation step
--   is still required to identify this subgroup with the full finite `PSL`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L885-L891
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L885-L891

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_indexColorQuotient
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (IndexCartwrightStegerImage P r level ⧸
          IndexCartwrightStegerColorZero P r level) =
      Nat.card (ResiduePowerClass P r level) := by sorry
