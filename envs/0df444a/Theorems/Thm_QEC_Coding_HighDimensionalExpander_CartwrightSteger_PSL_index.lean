-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_PSL_index
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:42:07.373354+00:00
-- url     : https://prove2.me/theorems/f0732ea1-9458-4c52-8cb5-1715dd10b16d
-- title:
--   Cartwright Steger: PSL index
-- statement:
--   Exact projective index for every selected hierarchy level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L185-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Index.lean#L185-L203

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_index
    (P : BasePrime) (r : Rank) (level : Nat) :
    (PSL P r level).index =
      (Fintype.card (ResidueField P r level) - 1).gcd r.matrixRank := by sorry
