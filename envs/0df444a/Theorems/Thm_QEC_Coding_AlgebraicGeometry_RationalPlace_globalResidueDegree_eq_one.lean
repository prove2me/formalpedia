-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_globalResidueDegree_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.RationalPlace.globalResidueDegree_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:20:07.997796+00:00
-- url     : https://prove2.me/theorems/4401a762-095f-4235-8126-8c26964329ed
-- title:
--   Rational Place: global Residue Degree eq one
-- statement:
--   A rational global place has degree one for the all-place degree used by
--   global divisors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlaceDegree.lean#L654-L700
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalPlaceDegree.lean#L654-L700

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlaceDegree
set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open MonoidWithZeroHom
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry

theorem QEC.Coding.AlgebraicGeometry.RationalPlace.globalResidueDegree_eq_one
    {k F : Type*} [Field k] [Finite k] [Field F] [κ : Algebra k F]
    [π : Algebra k[X] F] [ρ : Algebra k⟮X⟯ F]
    [τ : IsScalarTower k[X] k⟮X⟯ F] [φ : _root_.FunctionField k F]
    [σ : Algebra.IsSeparable k⟮X⟯ F]
    (Q : RationalPlace k F) :
    GlobalPlace.residueDegree Q.place = 1 := by sorry
