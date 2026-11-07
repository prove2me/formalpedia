-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_natCard_indexColorQuotient_eq_gcd
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_indexColorQuotient_eq_gcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:10.905233+00:00
-- url     : https://prove2.me/theorems/c51be0af-52b1-4362-9405-b961bbd8cec2
-- title:
--   Cartwright Steger: nat Card index Color Quotient eq gcd
-- statement:
--   Numerical form of the controlled index from LSV Proposition 6.7.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L894-L911
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L894-L911

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.natCard_indexColorQuotient_eq_gcd
    (P : BasePrime) (r : Rank) (level : Nat) :
    Nat.card
        (IndexCartwrightStegerImage P r level ⧸
          IndexCartwrightStegerColorZero P r level) =
      (Fintype.card (ResidueField P r level) - 1).gcd
        r.matrixRank := by sorry
