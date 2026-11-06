-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_valuation_algebraMap_of_integral
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.valuation_algebraMap_of_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:09:36.507213+00:00
-- url     : https://prove2.me/theorems/7c21948d-1ac3-4737-acfc-0d83769a7662
-- title:
--   Affine Place: valuation algebra Map of integral
-- statement:
--   The explicit field-embedding form of the affine valuation comparison.
--   This is the public boundary for clients whose terms already use the integral
--   closure map into `F`, such as the affine-to-global order bridge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlace.lean#L65-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlace.lean#L65-L70

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.valuation_algebraMap_of_integral (P : carrier k F)
    (x : _root_.FunctionField.ringOfIntegers k F) :
    valuation k F P
        (algebraMap (_root_.FunctionField.ringOfIntegers k F) F x) =
      P.intValuation x := by sorry
