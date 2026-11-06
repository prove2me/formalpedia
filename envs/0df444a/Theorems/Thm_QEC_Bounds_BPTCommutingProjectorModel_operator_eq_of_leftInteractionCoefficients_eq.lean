-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_operator_eq_of_leftInteractionCoefficients_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.operator_eq_of_leftInteractionCoefficients_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:00:57.550227+00:00
-- url     : https://prove2.me/theorems/b2a6a60e-b48f-4f56-88a0-c327093b923f
-- title:
--   BPTCommuting Projector Model: operator eq of left Interaction Coefficients eq
-- statement:
--   The left interaction coefficients determine an operator on `A tensor B`.
--   This is the coefficientwise reconstruction principle used to turn the
--   isotypic `B' tensor B''` actions back into an equality of the source
--   projectors, rather than leaving the block factorization at matrix-element
--   level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1600-L1652
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1600-L1652

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

theorem QEC.Bounds.BPTCommutingProjectorModel.operator_eq_of_leftInteractionCoefficients_eq
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P Q : Semantics.Operator (Semantics.CompositeSystem A B))
    (hcoefficients : ∀ a a' : A,
      leftInteractionCoefficient P a a' = leftInteractionCoefficient Q a a') :
    P = Q := by sorry
