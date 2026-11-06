-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_overlapLeftEmbedding_comp_overlapLeftEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapLeftEmbedding_comp_overlapLeftEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:12:59.626215+00:00
-- url     : https://prove2.me/theorems/42ca313c-d6fa-4f41-81d4-caf5f7beb4bf
-- title:
--   BPTCommuting Projector Model: adjoint overlap Left Embedding comp overlap Left Embedding
-- statement:
--   The fixed-left-factor embedding is an isometry for a normalized vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1687-L1699
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1687-L1699

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapLeftEmbedding_comp_overlapLeftEmbedding
    (A B : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (a a' : A) :
    (LinearMap.adjoint (overlapLeftEmbedding A B a)).comp
      (overlapLeftEmbedding A B a') =
        (inner Complex a a') • (1 : Semantics.Operator B) := by sorry
