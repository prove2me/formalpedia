-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicCopyTensorCoordinates_intertwines
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicCopyTensorCoordinates_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:25:31.360386+00:00
-- url     : https://prove2.me/theorems/1ad1a1b4-aea3-4662-963e-ba0b5dc3f53d
-- title:
--   BPTCommuting Projector Model: isotypic Copy Tensor Coordinates intertwines
-- statement:
--   The canonical copy-to-tensor coordinates intertwine the diagonal left action
--   with the literal simple-factor tensor action.  This is the operator equality
--   that turns the isotypic module statement into the left half of the BV03 block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3509-L3536
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3509-L3536

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicCopyTensorCoordinates_intertwines
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (operator : S) :
    (isotypicCopyTensorCoordinates S W n).toLinearMap.comp
        (isotypicLeftActionOnCopies S W n operator) =
      (isotypicTensorLeftAction S W n operator).comp
        (isotypicCopyTensorCoordinates S W n).toLinearMap := by sorry
