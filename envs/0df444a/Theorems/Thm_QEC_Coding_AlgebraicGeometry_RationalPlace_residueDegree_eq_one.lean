-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_residueDegree_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.RationalPlace.residueDegree_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:13:56.949287+00:00
-- url     : https://prove2.me/theorems/2a7ec1f0-ab37-40a6-b5d1-efe5743bea36
-- title:
--   Rational Place: residue Degree eq one
-- statement:
--   A rational place has residue degree one.  The degree is the conditional
--   `finrank` construction above, so this theorem does not introduce a general
--   finiteness assumption on residue fields.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L166-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlace.lean#L166-L175

import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RationalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.RationalPlace.residueDegree_eq_one (Q : RationalPlace k F) :
    GlobalPlace.residueDegreeOfFinite Q.place Q.hasFiniteResidueDegree = 1 := by sorry
