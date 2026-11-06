-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residue_eq_zero_iff
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.residue_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:09.598085+00:00
-- url     : https://prove2.me/theorems/ed6da110-b8aa-4626-8fb4-a225e427ac01
-- title:
--   Affine Place: residue eq zero iff
-- statement:
--   An integral element reduces to zero exactly when it belongs to the prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlace.lean#L47-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlace.lean#L47-L54

import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlace
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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.residue_eq_zero_iff (P : carrier k F)
    (x : _root_.FunctionField.ringOfIntegers k F) :
    residue k F P x = 0 ↔ x ∈ P.asIdeal := by sorry
