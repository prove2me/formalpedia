-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseSimplePoleTraceResidue_functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_infinityFibre
-- name    : QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue.functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_infinityFibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:53:59.473165+00:00
-- url     : https://prove2.me/theorems/297f3763-37c4-4a6c-926f-4763b4dee3f6
-- title:
--   Inverse Simple Pole Trace Residue: function Field Differential Trace simple Pole Trace Residue eq sum infinity Fibre
-- statement:
--   Trace--residue compatibility over the actual inverse fibre.  If a
--   differential has at most a simple pole at every place over rational infinity,
--   then its differential trace has at most a simple pole at rational infinity,
--   and its traced residue is the sum of the traced residues in that fibre.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/SimplePoleTraceResidue.lean#L1100-L1243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Residues/Inverse/SimplePoleTraceResidue.lean#L1100-L1243

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Direct_SimplePoleTraceResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_DifferentialTraceTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_FibreDirectFactor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Inverse_SimplePoleTraceResidue
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue
open scoped Polynomial RatFunc BigOperators
open FunctionFieldDifferential
open UniqueFactorizationMonoid
variable {k : Type*} [Field k] [Finite k]
variable {F : Type*} [Field F]
variable [oldPolynomialAlgebra : Algebra k[X] F]
variable [oldRationalAlgebra : Algebra (RatFunc k) F]
variable [oldScalarTower : IsScalarTower k[X] (RatFunc k) F]
variable [oldFunctionField : _root_.FunctionField k F]
variable [oldSeparable : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue.directConstantAlgebra
attribute [local instance] directConstantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue.directConstantScalarTower
attribute [local instance] directConstantScalarTower
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

theorem QEC.Coding.AlgebraicGeometry.InverseSimplePoleTraceResidue.functionFieldDifferentialTrace_simplePoleTraceResidue_eq_sum_infinityFibre
    (omega : Differential k F)
    (homega : ∀ D : InverseAffinePlace.infinityFibre
      (oldRationalAlgebra := oldRationalAlgebra) k F,
      omega ∈ Differential.simplePoleDifferentialLattice
        (InverseAffinePlace.infinityFibreGlobalPlace
          (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra)
          (τ := oldScalarTower) (φ := oldFunctionField)
          (σ := oldSeparable) (k := k) (F := F) D)) :
    ∃ htrace : functionFieldDifferentialTrace (k := k) (F := F) omega ∈
        Differential.simplePoleDifferentialLattice
          (GlobalPlace.rationalInfinity k),
      Differential.simplePoleTraceResidue (k := k) (F := RatFunc k)
          (GlobalPlace.rationalInfinity k)
          (functionFieldDifferentialTrace (k := k) (F := F) omega) htrace =
        ∑ D : InverseAffinePlace.infinityFibre
            (oldRationalAlgebra := oldRationalAlgebra) k F,
          Differential.simplePoleTraceResidue (k := k) (F := F)
            (InverseAffinePlace.infinityFibreGlobalPlace
              (π := oldPolynomialAlgebra) (ρ := oldRationalAlgebra)
              (τ := oldScalarTower) (φ := oldFunctionField)
              (σ := oldSeparable) (k := k) (F := F) D)
            omega (homega D) := by sorry
