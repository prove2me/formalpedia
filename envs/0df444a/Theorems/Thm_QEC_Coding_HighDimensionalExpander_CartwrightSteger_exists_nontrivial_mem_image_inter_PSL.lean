-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_nontrivial_mem_image_inter_PSL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_nontrivial_mem_image_inter_PSL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:48:35.308571+00:00
-- url     : https://prove2.me/theorems/e8731977-ecf1-4884-88e7-7721deb53488
-- title:
--   Cartwright Steger: exists nontrivial mem image inter PSL
-- statement:
--   The generated image has a construction-owned nonidentity element in
--   `PSL`, obtained as the ratio of two distinct Cartwright--Steger generators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L760-L785
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L760-L785

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_nontrivial_mem_image_inter_PSL
    (P : BasePrime) (r : Rank) (level : Nat) :
    ∃ g : PGL P r level,
      g ∈ IndexCartwrightStegerImage P r level ∧
      g ∈ PSL P r level ∧ g ≠ 1 := by sorry
