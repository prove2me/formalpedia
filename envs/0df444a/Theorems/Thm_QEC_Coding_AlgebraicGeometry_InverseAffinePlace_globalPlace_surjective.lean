-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_globalPlace_surjective
-- name    : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:14:13.085873+00:00
-- url     : https://prove2.me/theorems/fcb11a83-5044-422f-9027-2ec54765f0ce
-- title:
--   Inverse Affine Place: global Place surjective
-- statement:
--   The inverse-chart fibre's global valuation is surjective onto the
--   normalized integer value group, inherited from the existing height-one-prime
--   adic valuation rather than assumed for a new place structure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseInfinityFibre.lean#L250-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/InverseInfinityFibre.lean#L250-L268

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_globalPlace_surjective

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

theorem QEC.Coding.AlgebraicGeometry.InverseAffinePlace.globalPlace_surjective (v : infinityFibre (k := k) (F := F)
    (oldRationalAlgebra := oldRationalAlgebra)) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    letI : Algebra k F := AffinePlace.constantAlgebra k F
    Function.Surjective
      (globalPlace (k := k) (F := F) (oldRationalAlgebra := oldRationalAlgebra)
        (oldFunctionField := oldFunctionField) (oldSeparable := oldSeparable) v).valuation := by sorry
