-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_directFactorGlobalPlace_infinityFibreEquiv
-- name    : QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.directFactorGlobalPlace_infinityFibreEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:38:57.126222+00:00
-- url     : https://prove2.me/theorems/36ec1c25-eb79-4c9d-959f-3ea99b7770a7
-- title:
--   Inverse Fibre Direct Factor: direct Factor Global Place infinity Fibre Equiv
-- statement:
--   The direct global-place constructor at the corresponding factor is the
--   raw inverse-fibre global place itself.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/FibreDirectFactor.lean#L149-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/FibreDirectFactor.lean#L149-L173

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_IntegralDifferentialResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor
open scoped Polynomial RatFunc
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra k⟮X⟯ F]
variable [oldScalarTower : IsScalarTower k[X] k⟮X⟯ F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable k⟮X⟯ F]
local notation3 "inverseRationalAlgebra" =>
  InverseAffinePlace.transportedRationalAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inversePolynomialAlgebra" =>
  InverseAffinePlace.transportedPolynomialAlgebra
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseScalarTower" =>
  InverseAffinePlace.transportedScalarTower
    (oldRationalAlgebra := oldRationalAlgebra) k F
local notation3 "inverseFunctionField" =>
  InverseAffinePlace.transportedFunctionField
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldFunctionField := oldFunctionField) k F
local notation3 "inverseIsSeparable" =>
  InverseAffinePlace.transportedIsSeparable
    (oldRationalAlgebra := oldRationalAlgebra)
    (oldSeparable := oldSeparable) k F
omit oldPolynomialAlgebra oldScalarTower

theorem QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.directFactorGlobalPlace_infinityFibreEquiv
    (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    AffinePlace.globalPlace k F
        (DirectIntegralDifferentialResidue.directFactorPlace k F
          (Polynomial.idealX k)
          (infinityFibreEquivDirectFactors
            (oldRationalAlgebra := oldRationalAlgebra) k F D)) =
      InverseAffinePlace.globalPlace
        (oldRationalAlgebra := oldRationalAlgebra) k F D := by sorry
