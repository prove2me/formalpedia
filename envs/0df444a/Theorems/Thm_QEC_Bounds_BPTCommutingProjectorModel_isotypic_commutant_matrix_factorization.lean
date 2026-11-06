-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypic_commutant_matrix_factorization
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isotypic_commutant_matrix_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:08:47.289222+00:00
-- url     : https://prove2.me/theorems/e0f133c4-a52e-42ea-937d-cfc7720de87b
-- title:
--   BPTCommuting Projector Model: isotypic commutant matrix factorization
-- statement:
--   On an isotypic finite block, every endomorphism commuting with the interaction
--   algebra is a matrix acting only on the multiplicity coordinate.  Schur's lemma
--   makes each matrix entry scalar on the simple factor.  This is the right-factor
--   half of the tensor-block equality in `commuting_overlap_block_factorization`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2867-L2923
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2867-L2923

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isotypic_commutant_matrix_factorization
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B))
    (W : Submodule S B) [IsSimpleModule S W]
    (n : Nat) (T : Module.End S (Fin n → W)) :
    ∃ matrix : Matrix (Fin n) (Fin n) Complex,
      ∀ (vector : Fin n → W) (row : Fin n),
        T vector row = ∑ column, matrix row column • vector column := by sorry
