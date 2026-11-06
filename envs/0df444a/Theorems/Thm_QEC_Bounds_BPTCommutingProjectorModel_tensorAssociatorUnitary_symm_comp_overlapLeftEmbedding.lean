-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_symm_comp_overlapLeftEmbedding
-- name    : QEC.Bounds.BPTCommutingProjectorModel.tensorAssociatorUnitary_symm_comp_overlapLeftEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:00:47.188345+00:00
-- url     : https://prove2.me/theorems/4380d670-98e2-4f63-a5bd-2d7a94363e03
-- title:
--   BPTCommuting Projector Model: tensor Associator Unitary symm comp overlap Left Embedding
-- statement:
--   Reassociating `A tensor (W tensor N)` and then fixing the `A` factor is the
--   same map as first fixing `A` inside `A tensor W` and tensoring with `N`.
--   This naturality identity lets the coefficient reconstruction below keep the
--   full operator equality in its source parenthesization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1142-L1157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L1142-L1157

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

theorem QEC.Bounds.BPTCommutingProjectorModel.tensorAssociatorUnitary_symm_comp_overlapLeftEmbedding
    (A W N : Type u)
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    (a : A) :
    (tensorAssociatorUnitary A W N).symm.toLinearEquiv.toLinearMap.comp
      (overlapLeftEmbedding A (Semantics.CompositeSystem W N) a) =
        TensorProduct.map (overlapLeftEmbedding A W a) (1 : Semantics.Operator N) := by sorry
