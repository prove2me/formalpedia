-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetric_of_overlapLiftLeft
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetric_of_overlapLiftLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:27.158341+00:00
-- url     : https://prove2.me/theorems/cb3ce87c-f8eb-413e-85dd-6876a066c901
-- title:
--   BPTCommuting Projector Model: is Symmetric of overlap Lift Left
-- statement:
--   A normalized exterior vector reflects symmetry through the left overlap lift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3115-L3126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3115-L3126

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetric_of_overlapLiftLeft
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (eta : C) (heta : ‖eta‖ = 1)
    (h : (overlapLiftLeft (C := C) P).IsSymmetric) : P.IsSymmetric := by sorry
