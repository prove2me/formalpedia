-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_divisorDegree_eq
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.divisorDegree_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:13:39.627128+00:00
-- url     : https://prove2.me/theorems/4ef0c846-032a-416f-aad6-ca708883d126
-- title:
--   Affine Place: divisor Degree eq
-- statement:
--   Affine divisor degree is definitionally the generic divisor degree with
--   the constructed residue-degree coefficient function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlaceDegree.lean#L117-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlaceDegree.lean#L117-L119

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.divisorDegree_eq (D : Divisor (carrier k F)) :
    divisorDegree k F D = Divisor.degree (residueDegree k F) D := by sorry
