-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_starProduct_le_agEvaluationCode_add
-- name    : QEC.Coding.AlgebraicGeometry.starProduct_le_agEvaluationCode_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:26:39.031196+00:00
-- url     : https://prove2.me/theorems/942cb4be-45f7-49cc-ae3a-b9276f921be7
-- title:
--   Algebraic Geometry: star Product le ag Evaluation Code add
-- statement:
--   The actual star-product submodule of two evaluation codes is contained in
--   the evaluation code for the sum divisor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Code.lean#L110-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Code.lean#L110-L137

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]

theorem QEC.Coding.AlgebraicGeometry.starProduct_le_agEvaluationCode_add [Fintype k]
    (G H : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hG : ∀ i, G (Q i).place = 0)
    (hH : ∀ i, H (Q i).place = 0) :
    agStarProduct (agEvaluationCode G Q hG) (agEvaluationCode H Q hH) ≤
      (agEvaluationCode (G + H) Q (evaluationSupport_add G H Q hG hH)).carrier := by sorry
