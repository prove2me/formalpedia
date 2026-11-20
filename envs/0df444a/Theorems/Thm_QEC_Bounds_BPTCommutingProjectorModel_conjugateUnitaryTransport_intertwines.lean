-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_conjugateUnitaryTransport_intertwines
-- name    : QEC.Bounds.BPTCommutingProjectorModel.conjugateUnitaryTransport_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:16:02.250894+00:00
-- url     : https://prove2.me/theorems/5cfb2620-ec5c-404d-9841-1e19f25c61b9
-- title:
--   BPTCommuting Projector Model: conjugate Unitary Transport intertwines
-- statement:
--   A coordinate conjugate intertwines its original and transported unitaries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L223-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L223-L234

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u

theorem QEC.Bounds.BPTCommutingProjectorModel.conjugateUnitaryTransport_intertwines
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport H K) (V : Semantics.UnitaryTransport K K) :
    T.toLinearEquiv.toLinearMap.comp
        (conjugateUnitaryTransport T V).toLinearEquiv.toLinearMap =
      V.toLinearEquiv.toLinearMap.comp T.toLinearEquiv.toLinearMap := by sorry
