-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryLTensor_conj_tensorMap
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitaryLTensor_conj_tensorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:30:52.399205+00:00
-- url     : https://prove2.me/theorems/ae7ad9a6-b720-4b32-a374-2ee130fa33bf
-- title:
--   BPTCommuting Projector Model: unitary LTensor conj tensor Map
-- statement:
--   Left tensoring conjugates an arbitrary two-factor operator on its right factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L206-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L206-L220

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_BlockTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.unitaryLTensor_conj_tensorMap
    {H K I : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup I] [InnerProductSpace Complex I] [Semantics.FiniteQuantumSystem I]
    (U : Semantics.UnitaryTransport H K)
    (P : Semantics.Operator I) (Q : Semantics.Operator H) :
    (unitaryLTensor I U).conjOperator (TensorProduct.map P Q) =
      TensorProduct.map P (U.conjOperator Q) := by sorry
