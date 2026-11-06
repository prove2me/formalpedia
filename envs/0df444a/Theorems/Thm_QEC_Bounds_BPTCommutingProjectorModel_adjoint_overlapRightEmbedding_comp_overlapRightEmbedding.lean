-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_overlapRightEmbedding_comp_overlapRightEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapRightEmbedding_comp_overlapRightEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:12:11.394385+00:00
-- url     : https://prove2.me/theorems/4ba511c0-00b4-4e8f-a99d-132cebf515d0
-- title:
--   BPTCommuting Projector Model: adjoint overlap Right Embedding comp overlap Right Embedding
-- statement:
--   The fixed-right-factor embedding is an isometry exactly when its chosen
--   right-factor vector has unit norm.  This elementary contraction identity is
--   the reconstruction mechanism for a BV03 tensor block: after the interaction
--   coefficients have been shown to act as `L tensor 1`, contracting the inert
--   factor produces the left block operator without making any spectral choice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1091-L1103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1091-L1103

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapRightEmbedding_comp_overlapRightEmbedding
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (b b' : B) :
    (LinearMap.adjoint (overlapRightEmbedding A B b)).comp
      (overlapRightEmbedding A B b') =
        (inner Complex b b') • (1 : Semantics.Operator A) := by sorry
