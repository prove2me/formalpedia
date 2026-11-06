-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_symm_comp_nestedOverlapRightEmbeddings
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorAssociatorUnitary_symm_comp_nestedOverlapRightEmbeddings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:24:05.286122+00:00
-- url     : https://prove2.me/theorems/1c916455-4c0a-4ab0-a274-01b6a5b91f2f
-- title:
--   BPTCommuting Projector Model: tensor Associator Unitary symm comp nested Overlap Right Embeddings
-- statement:
--   Reassociation identifies the nested right embeddings used by right coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1781-L1794
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1781-L1794

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorAssociatorUnitary_symm_comp_nestedOverlapRightEmbeddings
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (eta : W) (c : C) :
    (tensorAssociatorUnitary W N C).symm.toLinearEquiv.toLinearMap.comp
      ((overlapLeftEmbedding W (Semantics.CompositeSystem N C) eta).comp
        (overlapRightEmbedding N C c)) =
      (overlapRightEmbedding (Semantics.CompositeSystem W N) C c).comp
        (overlapLeftEmbedding W N eta) := by sorry
