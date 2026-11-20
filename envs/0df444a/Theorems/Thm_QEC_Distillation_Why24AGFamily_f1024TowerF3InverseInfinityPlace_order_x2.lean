-- Prove2me | Theorems.Thm_QEC_Distillation_Why24AGFamily_f1024TowerF3InverseInfinityPlace_order_x2
-- name    : QEC.Distillation.Why24AGFamily.f1024TowerF3InverseInfinityPlace_order_x2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:18:32.653888+00:00
-- url     : https://prove2.me/theorems/ea250d08-de48-4d6d-8621-faf66e3d73b8
-- title:
--   Why24 AGFamily: f1024 Tower F3 Inverse Infinity Place order x2
-- statement:
--   At every actual second-tower inverse-chart upper prime, the embedded
--   coordinate `x₂` has order `-32`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/AlgebraicGeometryFamily.lean#L1953-L1958
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/ConstantOverheadProtocol/AlgebraicGeometryFamily.lean#L1953-L1958

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

theorem QEC.Distillation.Why24AGFamily.f1024TowerF3InverseInfinityPlace_order_x2
    (P : QEC.Coding.AlgebraicGeometry.InverseAffinePlace.infinityFibre
      (k := F1024) (F := F1024TowerF3)) :
    f1024TowerF3InverseInfinityOrder P
      (algebraMap F1024TowerF2 F1024TowerF3 f1024TowerX2) = -32 := by sorry
