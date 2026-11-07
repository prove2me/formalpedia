-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypic_copy_tensor_unitary_intertwiner
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypic_copy_tensor_unitary_intertwiner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:26:08.707207+00:00
-- url     : https://prove2.me/theorems/3f965388-64b6-442e-9c54-0d711aa20707
-- title:
--   BPTCommuting Projector Model: isotypic copy tensor unitary intertwiner
-- statement:
--   Polar-normalize the canonical copy coordinates.  The resulting transport is
--   an actual unitary and conjugates every left interaction coefficient to an
--   operator of the form `actionOnW tensor 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3984-L4000
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3984-L4000

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypic_copy_tensor_unitary_intertwiner
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) :
    ∃ U : Semantics.UnitaryTransport
      (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex))
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)),
      ∀ operator : S,
        U.toLinearEquiv.toLinearMap.comp (isotypicLeftActionOnCopies S W n operator) =
          (isotypicTensorLeftAction S W n operator).comp U.toLinearEquiv.toLinearMap := by sorry
