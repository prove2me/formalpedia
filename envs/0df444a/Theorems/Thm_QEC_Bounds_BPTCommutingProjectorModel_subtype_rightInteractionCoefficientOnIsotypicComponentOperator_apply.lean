-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_subtype_rightInteractionCoefficientOnIsotypicComponentOperator_apply
-- name    : QEC.Bounds.BPTCommutingProjectorModel.subtype_rightInteractionCoefficientOnIsotypicComponentOperator_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:26:26.83585+00:00
-- url     : https://prove2.me/theorems/e0556379-b2bf-46e6-88a2-6c670689867d
-- title:
--   BPTCommuting Projector Model: subtype right Interaction Coefficient On Isotypic Component Operator apply
-- statement:
--   The sector action is the concrete right coefficient after subtype inclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4257-L4273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L4257-L4273

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.subtype_rightInteractionCoefficientOnIsotypicComponentOperator_apply
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) (c c' : C)
    (vector : component.1.restrictScalars Complex) :
    (component.1.restrictScalars Complex).subtype
      (rightInteractionCoefficientOnIsotypicComponentOperator P Q hselfAdjoint hcommute
        component c c' vector) =
      rightInteractionCoefficient Q c c'
        ((component.1.restrictScalars Complex).subtype vector) := by sorry
