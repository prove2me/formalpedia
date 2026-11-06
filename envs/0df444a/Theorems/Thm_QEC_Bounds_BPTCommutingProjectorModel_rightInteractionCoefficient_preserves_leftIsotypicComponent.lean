-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_rightInteractionCoefficient_preserves_leftIsotypicComponent
-- name    : QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficient_preserves_leftIsotypicComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:39:10.340895+00:00
-- url     : https://prove2.me/theorems/20a85056-ddd5-4b53-8756-640476a46f96
-- title:
--   BPTCommuting Projector Model: right Interaction Coefficient preserves left Isotypic Component
-- statement:
--   Every right interaction coefficient preserves every left-isotypic component.
--   The proof turns it into an `S`-module endomorphism using the commuting
--   interaction algebras, then uses full invariance of an isotypic component.
--   This is the direct-sum/block-diagonal step in the BV03 decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2542-L2567
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2542-L2567

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

theorem QEC.Bounds.BPTCommutingProjectorModel.rightInteractionCoefficient_preserves_leftIsotypicComponent
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (W : Submodule (leftInteractionAlgebra P) B) [IsSimpleModule (leftInteractionAlgebra P) W]
    (c c' : C) {vector : B}
    (hvector : vector ∈ isotypicComponent (leftInteractionAlgebra P) B W) :
    rightInteractionCoefficient Q c c' vector ∈
      isotypicComponent (leftInteractionAlgebra P) B W := by sorry
