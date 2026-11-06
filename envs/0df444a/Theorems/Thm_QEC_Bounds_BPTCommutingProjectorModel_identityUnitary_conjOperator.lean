-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_identityUnitary_conjOperator
-- name    : QEC.Bounds.BPTCommutingProjectorModel.identityUnitary_conjOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:44:23.953259+00:00
-- url     : https://prove2.me/theorems/937ef958-11cf-4a62-ae64-eec1bf5d2305
-- title:
--   BPTCommuting Projector Model: identity Unitary conj Operator
-- statement:
--   Conjugation by the identity transport leaves every operator unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L50-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L50-L54

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

theorem QEC.Bounds.BPTCommutingProjectorModel.identityUnitary_conjOperator (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (A : Semantics.Operator H) :
    (identityUnitary H).conjOperator A = A := by sorry
