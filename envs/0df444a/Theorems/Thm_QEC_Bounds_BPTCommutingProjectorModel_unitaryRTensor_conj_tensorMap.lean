-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_tensorMap
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitaryRTensor_conj_tensorMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:30:14.721833+00:00
-- url     : https://prove2.me/theorems/c011ce7f-4e3b-424a-9082-9d9e051d0686
-- title:
--   BPTCommuting Projector Model: unitary RTensor conj tensor Map
-- statement:
--   Right tensoring conjugates an arbitrary two-factor operator on its left factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L223-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/BlockTransport.lean#L223-L237

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

theorem QEC.Bounds.BPTCommutingProjectorModel.unitaryRTensor_conj_tensorMap
    {H K I : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup I] [InnerProductSpace Complex I] [Semantics.FiniteQuantumSystem I]
    (U : Semantics.UnitaryTransport H K)
    (P : Semantics.Operator H) (Q : Semantics.Operator I) :
    (unitaryRTensor U I).conjOperator (TensorProduct.map P Q) =
      TensorProduct.map (U.conjOperator P) Q := by sorry
