-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicMultiplicityMatrixActionOnFunctionCopies_single
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicMultiplicityMatrixActionOnFunctionCopies_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:25:38.672016+00:00
-- url     : https://prove2.me/theorems/54ee71dd-8e55-4796-81a8-56dde3eca192
-- title:
--   BPTCommuting Projector Model: isotypic Multiplicity Matrix Action On Function Copies single
-- statement:
--   A matrix sends one algebraic multiplicity basis vector to its matching column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3846-L3856
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3846-L3856

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicMultiplicityMatrixActionOnFunctionCopies_single
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) (n : Nat) (matrix : Matrix (Fin n) (Fin n) Complex)
    (i : Fin n) (w : W) :
    isotypicMultiplicityMatrixActionOnFunctionCopies S W n matrix (Pi.single i w) =
      ∑ row, Pi.single row (matrix row i • w) := by sorry
