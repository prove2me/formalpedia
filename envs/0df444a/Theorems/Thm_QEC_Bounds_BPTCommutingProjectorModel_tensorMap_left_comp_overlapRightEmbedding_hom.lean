-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorMap_left_comp_overlapRightEmbedding_hom
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorMap_left_comp_overlapRightEmbedding_hom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:09:05.138206+00:00
-- url     : https://prove2.me/theorems/84878ddb-afc5-401e-b4af-e81682d5dba4
-- title:
--   BPTCommuting Projector Model: tensor Map left comp overlap Right Embedding hom
-- statement:
--   A left tensor map carries fixed-right embeddings through the same left map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3165-L3176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3165-L3176

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorMap_left_comp_overlapRightEmbedding_hom
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (c : C) (Z : A →ₗ[Complex] B) :
    (TensorProduct.map Z (1 : Semantics.Operator C)).comp
      (overlapRightEmbedding A C c) =
        (overlapRightEmbedding B C c).comp Z := by sorry
