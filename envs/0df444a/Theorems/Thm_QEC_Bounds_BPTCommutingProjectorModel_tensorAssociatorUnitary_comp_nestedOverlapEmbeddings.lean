-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_comp_nestedOverlapEmbeddings
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorAssociatorUnitary_comp_nestedOverlapEmbeddings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:59.758552+00:00
-- url     : https://prove2.me/theorems/8fadf97c-8076-4493-8e7a-30a6134e1508
-- title:
--   BPTCommuting Projector Model: tensor Associator Unitary comp nested Overlap Embeddings
-- statement:
--   The associator sends the nested embedding of a `W` vector with fixed exterior
--   coordinates to the corresponding embedding in `A tensor (W tensor N)`.
--   This is the common coordinate identity which makes tensor-factor compression
--   commute with taking a left interaction coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1191-L1204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1191-L1204

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorAssociatorUnitary_comp_nestedOverlapEmbeddings
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (a : A) (eta : N) :
    (tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap.comp
      ((overlapRightEmbedding (Semantics.CompositeSystem A W) N eta).comp
        (overlapLeftEmbedding A W a)) =
      (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a).comp
        (overlapRightEmbedding W N eta) := by sorry
