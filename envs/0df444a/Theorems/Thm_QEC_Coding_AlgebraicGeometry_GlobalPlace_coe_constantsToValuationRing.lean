-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:44:58.608333+00:00
-- url     : https://prove2.me/theorems/6643e9a7-65c1-4a09-b8e1-06e66efc2e12
-- title:
--   Global Place: coe constants To Valuation Ring
-- statement:
--   The Global Place construction uses the coe constants To Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L37-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L37-L39

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing (P : GlobalPlace k F) (a : k) :
    ((constantsToValuationRing P a : valuationRing P) : F) = algebraMap k F a := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
