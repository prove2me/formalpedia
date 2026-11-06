-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_overlapLeftEmbedding_comp_tensorAssociatorUnitary
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapLeftEmbedding_comp_tensorAssociatorUnitary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:04:07.970746+00:00
-- url     : https://prove2.me/theorems/4ae52bac-a1f0-4e05-b91f-bfc3e0be2856
-- title:
--   BPTCommuting Projector Model: adjoint overlap Left Embedding comp tensor Associator Unitary
-- statement:
--   Taking adjoints of the preceding naturality equation moves the associator to
--   the other side of the coefficient sandwich.  This is the exact identity used
--   to factor a reconstructed overlap projector as `P_left tensor 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1164-L1183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1164-L1183

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_overlapLeftEmbedding_comp_tensorAssociatorUnitary
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (a : A) :
    (LinearMap.adjoint (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a)).comp
      (tensorAssociatorUnitary A W N).toLinearEquiv.toLinearMap =
        TensorProduct.map (LinearMap.adjoint (overlapLeftEmbedding A W a))
          (1 : Semantics.Operator N) := by sorry
