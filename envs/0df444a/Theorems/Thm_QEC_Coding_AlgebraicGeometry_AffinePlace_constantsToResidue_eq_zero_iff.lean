-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_constantsToResidue_eq_zero_iff
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.constantsToResidue_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:13:21.091108+00:00
-- url     : https://prove2.me/theorems/44ebdb55-c9a5-4adf-87ae-8e01e619883c
-- title:
--   Affine Place: constants To Residue eq zero iff
-- statement:
--   A constant reduces to zero at an affine place precisely when its image in
--   the integral closure belongs to the selected height-one prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineResidue.lean#L62-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineResidue.lean#L62-L69

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineResidue
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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.constantsToResidue_eq_zero_iff (P : carrier k F) (a : k) :
    constantsToResidue k F P a = 0 ↔
      algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) (Polynomial.C a) ∈
        P.asIdeal := by sorry
