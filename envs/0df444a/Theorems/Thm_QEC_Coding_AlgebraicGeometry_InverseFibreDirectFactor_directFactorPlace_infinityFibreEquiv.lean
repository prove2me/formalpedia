-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseFibreDirectFactor_directFactorPlace_infinityFibreEquiv
-- name    : QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.directFactorPlace_infinityFibreEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:38:20.375634+00:00
-- url     : https://prove2.me/theorems/099b89bd-7ed3-4ce8-807b-6d335bafd54d
-- title:
--   Inverse Fibre Direct Factor: direct Factor Place infinity Fibre Equiv
-- statement:
--   Reinterpreting an inverse-fibre point through the direct factor subtype
--   recovers the original height-one prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/FibreDirectFactor.lean#L123-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/FibreDirectFactor.lean#L123-L144

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

theorem QEC.Coding.AlgebraicGeometry.InverseFibreDirectFactor.directFactorPlace_infinityFibreEquiv
    (D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F) :
    letI : Algebra k⟮X⟯ F := inverseRationalAlgebra
    letI : Algebra k[X] F := inversePolynomialAlgebra
    letI : IsScalarTower k[X] k⟮X⟯ F := inverseScalarTower
    letI : _root_.FunctionField k F := inverseFunctionField
    letI : Algebra.IsSeparable k⟮X⟯ F := inverseIsSeparable
    DirectIntegralDifferentialResidue.directFactorPlace k F
        (Polynomial.idealX k)
        (infinityFibreEquivDirectFactors
          (oldRationalAlgebra := oldRationalAlgebra) k F D) = D.1 := by sorry
