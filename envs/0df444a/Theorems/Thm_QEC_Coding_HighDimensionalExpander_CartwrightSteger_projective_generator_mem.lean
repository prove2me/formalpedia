-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_projective_generator_mem
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.projective_generator_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:29:10.003212+00:00
-- url     : https://prove2.me/theorems/d5e3d260-a90d-4882-a5ca-efffff05e050
-- title:
--   Cartwright Steger: projective generator mem
-- statement:
--   The Cartwright Steger construction uses the projective generator mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L634-L639
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L634-L639

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.projective_generator_mem (P : BasePrime) (r : Rank)
    (u : ConstantProjectiveClass P r) :
    cartwrightStegerToProjective P r (cartwrightStegerGenerator P r u) ∈
      CartwrightStegerProjectiveGroup P r := by sorry
