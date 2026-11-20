-- Prove2me | Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024Why24OddAGCode_dimension
-- name    : QEC.Distillation.Why24AGFamily.f1024Why24OddAGCode_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:18:26.334586+00:00
-- url     : https://prove2.me/theorems/492022b5-4b9a-4204-975a-dba8b093814e
-- title:
--   Why24 AGFamily: f1024 Why24 Odd AGCode dimension
-- statement:
--   The retained code has the exact large-degree Riemann--Roch dimension
--   `a + 1 - g`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/AlgebraicGeometryFamily.lean#L12055-L12084
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/AlgebraicGeometryFamily.lean#L12055-L12084

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
attribute [instance] F1024TowerFiniteChartData.commRingInst
  F1024TowerFiniteChartData.domainInst
  F1024TowerFiniteChartData.dedekindInst
  F1024TowerFiniteChartData.constantAlgebraInst
  F1024TowerFiniteChartData.actualAlgebraInst
  F1024TowerFiniteChartData.constantTowerInst
  F1024TowerFiniteChartData.fractionRingInst
open QEC.Coding.AlgebraicGeometry
attribute [local instance 2000] QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantAlgebra
attribute [local instance 2000] QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantScalarTower
attribute [local instance 2000] QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantAlgebra QEC.Distillation.Why24AGFamily.f1024Why24OddDirectConstantScalarTower

theorem QEC.Distillation.Why24AGFamily.f1024Why24OddAGCode_dimension (r : ℕ) :
    (QEC.Coding.Dimension (f1024Why24OddAGCode r) : ℤ) =
      (selectedDivisorDegree (oddGenus r) : ℤ) + 1 - oddGenus r := by sorry
