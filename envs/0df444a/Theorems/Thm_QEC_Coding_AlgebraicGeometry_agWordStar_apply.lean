-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agWordStar_apply
-- name    : QEC.Coding.AlgebraicGeometry.agWordStar_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:24:20.05811+00:00
-- url     : https://prove2.me/theorems/a63375e8-1bf0-4528-8c5a-6e15580c1166
-- title:
--   Algebraic Geometry: ag Word Star apply
-- statement:
--   The Algebraic Geometry construction uses the ag Word Star apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Code.lean#L36-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/Code.lean#L36-L38

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
variable {k F ι : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Fintype ι]

theorem QEC.Coding.AlgebraicGeometry.agWordStar_apply (x y : Word k ι) (i : ι) :
    agWordStar x y i = x i * y i := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.agWordStar_apply
