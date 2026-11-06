-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_valuation_of_integral
-- name    : QEC.Coding.AlgebraicGeometry.AffinePlace.valuation_of_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:12:01.153781+00:00
-- url     : https://prove2.me/theorems/afba58b6-7847-4604-8aa7-39bad84c5fa3
-- title:
--   Affine Place: valuation of integral
-- statement:
--   The affine valuation agrees with its integral-domain adic valuation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlace.lean#L57-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/AffinePlace.lean#L57-L60

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

theorem QEC.Coding.AlgebraicGeometry.AffinePlace.valuation_of_integral (P : carrier k F)
    (x : _root_.FunctionField.ringOfIntegers k F) :
    valuation k F P x = P.intValuation x := by sorry
