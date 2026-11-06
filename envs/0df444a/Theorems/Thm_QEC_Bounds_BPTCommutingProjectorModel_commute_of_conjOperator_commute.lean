-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commute_of_conjOperator_commute
-- name    : QEC.Bounds.BPTCommutingProjectorModel.commute_of_conjOperator_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:18:27.572207+00:00
-- url     : https://prove2.me/theorems/35c184ca-bc43-46ce-be10-fe90a9b74a2e
-- title:
--   BPTCommuting Projector Model: commute of conj Operator commute
-- statement:
--   Commutation can be reflected through a unitary coordinate transport.  This is
--   used by the two BPT cuts to return a virtual sector commutation relation to
--   the physical local operator supplied to no-information.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3758-L3776
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L3758-L3776

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

theorem QEC.Bounds.BPTCommutingProjectorModel.commute_of_conjOperator_commute
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (U : Semantics.UnitaryTransport H K)
    {P Q : Semantics.Operator H}
    (h : Commute (U.conjOperator P) (U.conjOperator Q)) :
    Commute P Q := by sorry
