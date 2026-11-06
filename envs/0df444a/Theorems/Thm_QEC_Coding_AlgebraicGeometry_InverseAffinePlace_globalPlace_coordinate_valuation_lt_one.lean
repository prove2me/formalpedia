-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_globalPlace_coordinate_valuation_lt_one
-- name    : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace_coordinate_valuation_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:35.449307+00:00
-- url     : https://prove2.me/theorems/9818ca89-9289-42cf-8e50-bb81e39220d6
-- title:
--   Inverse Affine Place: global Place coordinate valuation lt one
-- statement:
--   The transported chart coordinate has valuation strictly below one at each
--   fibre point.  This is the exact adic form of its local zero condition; no
--   global place classification or comparison with the original coordinate is
--   asserted.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseInfinityFibre.lean#L274-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseInfinityFibre.lean#L274-L299

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

theorem QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace_coordinate_valuation_lt_one
    (v : infinityFibre (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    (globalPlace (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)
      (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable) v).valuation
      (algebraMap (_root_.FunctionField.ringOfIntegers k F) F
        (algebraMap k[X] (_root_.FunctionField.ringOfIntegers k F) Polynomial.X)) < 1 := by sorry
