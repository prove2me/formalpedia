-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_IndexCartwrightStegerColorZero_iff_mem_PSL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_IndexCartwrightStegerColorZero_iff_mem_PSL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:48:36.728868+00:00
-- url     : https://prove2.me/theorems/2c9f9a60-f05a-4720-bce7-3682840efbe9
-- title:
--   Cartwright Steger: mem Index Cartwright Steger Color Zero iff mem PSL
-- statement:
--   The Cartwright Steger construction uses the mem Index Cartwright Steger Color Zero iff mem PSL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L861-L869
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L861-L869

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_IndexCartwrightStegerColorZero_iff_mem_PSL
    (P : BasePrime) (r : Rank) (level : Nat)
    (g : IndexCartwrightStegerImage P r level) :
    g ∈ IndexCartwrightStegerColorZero P r level ↔
      (g : PGL P r level) ∈ PSL P r level := by sorry
