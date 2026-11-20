-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_conjOperator_eq_symm_conjOperator_of_transport
-- name    : QEC.Bounds.BPTCommutingProjectorModel.conjOperator_eq_symm_conjOperator_of_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:07:20.911089+00:00
-- url     : https://prove2.me/theorems/83d69c7a-3db5-4ef4-bbd1-9e0be551d6c3
-- title:
--   BPTCommuting Projector Model: conj Operator eq symm conj Operator of transport
-- statement:
--   The BPTCommuting Projector Model construction uses the conj Operator eq symm conj Operator of transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyTransportBasic.lean#L24-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyTransportBasic.lean#L24-L43

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransportBasic
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.conjOperator_eq_symm_conjOperator_of_transport
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport H K)
    (W : Semantics.UnitaryTransport H H)
    (V : Semantics.UnitaryTransport K K)
    (C : Semantics.Operator H) (P Q : Semantics.Operator K)
    (htransport : T.conjOperator (W.conjOperator C) =
      V.conjOperator (T.conjOperator C))
    (hproduct : V.conjOperator (T.conjOperator C) = P)
    (hbefore : P = Q) :
    W.conjOperator C = T.symm.conjOperator Q := by sorry
