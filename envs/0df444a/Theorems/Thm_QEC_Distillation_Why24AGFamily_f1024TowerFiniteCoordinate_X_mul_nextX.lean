-- Prove2me | Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024TowerFiniteCoordinate_X_mul_nextX
-- name    : QEC.Distillation.Why24AGFamily.f1024TowerFiniteCoordinate_X_mul_nextX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:19:14.568195+00:00
-- url     : https://prove2.me/theorems/faa40977-b785-4788-ac12-f099cb7466df
-- title:
--   Why24 AGFamily: f1024 Tower Finite Coordinate X mul next X
-- statement:
--   The evaluated source change of coordinates is exact at every finite
--   successor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/AlgebraicGeometryFamily.lean#L3493-L3500
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/AlgebraicGeometryFamily.lean#L3493-L3500

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Data.Fin.Rev
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_FullConstantField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GarciaStichtenothParameters
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_QuditQubitConversion_FiniteField
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_WeightedTriorthogonalCSS
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_AlgebraicGeometryFamily
set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.Why24AGFamily
open QEC.Coding
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open scoped Polynomial.Bivariate WithZero
open Polynomial
noncomputable section
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024CharTwo
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerF2CharTwo
attribute [local instance] QEC.Distillation.Why24AGFamily.f1024TowerF3CharTwo
attribute [instance] F1024TowerStageData.fieldInst
  F1024TowerStageData.rationalAlgebraInst
  F1024TowerStageData.finiteDimensionalInst
  F1024TowerStageData.separableInst
  F1024TowerStageData.constantAlgebraInst
  F1024TowerStageData.constantRationalTowerInst
  F1024TowerStageData.polynomialAlgebraInst
  F1024TowerStageData.polynomialRationalTowerInst
  F1024TowerStageData.charTwoInst

theorem QEC.Distillation.Why24AGFamily.f1024TowerFiniteCoordinate_X_mul_nextX {height : ℕ}
    (coordinate : F1024TowerFiniteCoordinate (height + 1)) :
    f1024TowerFiniteCoordinateValue
          (f1024TowerFiniteCoordinatePrefix coordinate) *
        f1024TowerFiniteCoordinateValue coordinate =
      f1024TowerFiniteCoordinateStepZ coordinate := by sorry
