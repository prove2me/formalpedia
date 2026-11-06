-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residueDegree_eq_generator_natDegree_mul_inertia
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.residueDegree_eq_generator_natDegree_mul_inertia
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:11.348447+00:00
-- url     : https://prove2.me/theorems/2d73a76d-2505-43c0-919e-2cd8fced7bbd
-- title:
--   Affine Place: residue Degree eq generator nat Degree mul inertia
-- statement:
--   The degree of an affine place over a finite constant field factors as the
--   degree of its contracted polynomial prime times the inertia degree upstairs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectNormCount.lean#L99-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectNormCount.lean#L99-L146

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.AffinePlace
open scoped Polynomial RatFunc nonZeroDivisors
open Submodule.IsPrincipal
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.residueDegree_eq_generator_natDegree_mul_inertia
    (P : carrier k F) :
    residueDegree k F P =
      (generator (basePrime k F P)).natDegree *
        (basePrime k F P).inertiaDeg' P.asIdeal := by sorry
