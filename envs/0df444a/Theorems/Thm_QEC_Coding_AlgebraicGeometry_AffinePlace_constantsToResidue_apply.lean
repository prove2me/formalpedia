-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_constantsToResidue_apply
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.constantsToResidue_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:13:00.39395+00:00
-- url     : https://prove2.me/theorems/116c49f8-0694-41ec-9753-dc57bedc14f2
-- title:
--   Affine Place: constants To Residue apply
-- statement:
--   Unfolding the affine constant-reduction map exposes its two genuine
--   intermediate maps.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineResidue.lean#L54-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffineResidue.lean#L54-L58

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.constantsToResidue_apply (P : carrier k F) (a : k) :
    constantsToResidue k F P a =
      algebraMap (_root_.FunctionField.ringOfIntegers k F) (residueField k F P)
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) (Polynomial.C a)) := by sorry
