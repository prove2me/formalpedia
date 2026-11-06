-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypic_star_unitary_intertwiner
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypic_star_unitary_intertwiner
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T13:25:29.539475+00:00
-- url     : https://prove2.me/theorems/32d4c3f4-e234-436c-8fcd-03fc78196d88
-- title:
--   BPTCommuting Projector Model: isotypic star unitary intertwiner
-- statement:
--   The isotypic coordinate equivalence can be chosen unitary while retaining its
--   exact left-interaction-algebra intertwining equation.  The underlying
--   `S`-linear equivalence is polar-normalized through its positive Gram operator;
--   the resulting transport is the boundary-coordinate unitary used by the BV03
--   overlap block equality below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3378-L3421
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3378-L3421

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypic_star_unitary_intertwiner
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (component : isotypicComponents S B) (n : Nat) (W : Submodule S B)
    (e : component.1 ≃ₗ[S] (Fin n → W)) :
    ∃ U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (PiLp 2 (fun _ : Fin n => W.restrictScalars Complex)),
      ∀ operator : S,
        U.toLinearEquiv.toLinearMap.comp (isotypicLeftAction S component operator) =
          (isotypicLeftActionOnCopies S W n operator).comp U.toLinearEquiv.toLinearMap := by sorry
