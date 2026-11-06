-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_conjOperator_iff
-- name    : QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_conjOperator_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:15:48.202445+00:00
-- url     : https://prove2.me/theorems/07c482a2-cf6b-43b7-8c4c-ff6ef9a373aa
-- title:
--   BPTCommuting Projector Model: is Symmetric Projection conj Operator iff
-- statement:
--   Unitary conjugation preserves and reflects orthogonal-projection structure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3705-L3729
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3705-L3729

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

theorem QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_conjOperator_iff
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K) (P : Semantics.Operator H) :
    (U.conjOperator P).IsSymmetricProjection ↔ P.IsSymmetricProjection := by sorry
