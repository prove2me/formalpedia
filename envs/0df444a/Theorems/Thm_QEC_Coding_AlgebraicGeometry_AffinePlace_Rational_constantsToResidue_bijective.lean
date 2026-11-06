-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_Rational_constantsToResidue_bijective
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.Rational.constantsToResidue_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:13:44.988654+00:00
-- url     : https://prove2.me/theorems/b8c352e9-99d3-4808-9ce5-ebee2fabf60e
-- title:
--   Rational: constants To Residue bijective
-- statement:
--   At an affine rational place, the canonical constant-reduction map is
--   bijective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlaceDegree.lean#L139-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlaceDegree.lean#L139-L149

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_Divisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.AffinePlace
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
open QEC.Coding.AlgebraicGeometry.AffinePlace.Rational

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.Rational.constantsToResidue_bijective {P : carrier k F} (Q : Rational k F P) :
    Function.Bijective (constantsToResidue k F P) := by sorry
