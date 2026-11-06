-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_coordinate_mem_definingPrime
-- name    : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.coordinate_mem_definingPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:33.288756+00:00
-- url     : https://prove2.me/theorems/88184e8a-fdc8-4bf0-8935-55e68c1cbe6c
-- title:
--   Inverse Affine Place: coordinate mem defining Prime
-- statement:
--   The transported inverse-chart coordinate, as an element of its integral
--   closure, belongs to every prime in the raw fibre.  This is the local zero
--   condition above `(X)`; it does not identify the resulting global place with
--   any place from the original affine chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseInfinityFibre.lean#L187-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseInfinityFibre.lean#L187-L204

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.InverseAffinePlace
open scoped Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
local notation3 "inverseRationalAlgebra" =>
  transportedRationalAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inversePolynomialAlgebra" =>
  transportedPolynomialAlgebra (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inverseScalarTower" =>
  transportedScalarTower (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
local notation3 "inverseFunctionField" =>
  transportedFunctionField (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField)
local notation3 "inverseIsSeparable" =>
  transportedIsSeparable (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable)
local notation3 "inverseCarrier" =>
  carrier (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)
omit [Finite k]

theorem QEC.Coding.AlgebraicGeometry.InverseAffinePlace.coordinate_mem_definingPrime (v : infinityFibre (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X ∈ v.1.asIdeal := by sorry
