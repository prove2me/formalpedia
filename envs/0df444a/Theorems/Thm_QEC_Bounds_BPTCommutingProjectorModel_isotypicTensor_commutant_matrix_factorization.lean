-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicTensor_commutant_matrix_factorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypicTensor_commutant_matrix_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:26:15.63174+00:00
-- url     : https://prove2.me/theorems/10777d2a-a606-45d6-b754-72b5dcbe2fba
-- title:
--   BPTCommuting Projector Model: isotypic Tensor commutant matrix factorization
-- statement:
--   An operator commuting with the left action on one finite simple isotypic block
--   is exactly `1 tensor R` after the concrete tensor coordinates.  This is the
--   right-factor equality required by the BV03 overlap decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3899-L3942
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L3899-L3942

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypicTensor_commutant_matrix_factorization
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) [IsSimpleModule S W]
    (n : Nat)
    (T : Semantics.Operator
      (W.restrictScalars Complex ⊗[Complex] EuclideanSpace Complex (Fin n)))
    (hcommute : ∀ operator : S, Commute T (isotypicTensorLeftAction S W n operator)) :
    ∃ matrix : Matrix (Fin n) (Fin n) Complex,
      T = TensorProduct.map (1 : Semantics.Operator (W.restrictScalars Complex))
        (isotypicMultiplicityMatrixOperator n matrix) := by sorry
