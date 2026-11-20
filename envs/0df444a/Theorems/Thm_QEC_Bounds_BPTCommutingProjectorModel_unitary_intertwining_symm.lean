-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitary_intertwining_symm
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitary_intertwining_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:15:54.16729+00:00
-- url     : https://prove2.me/theorems/1dcba1cc-3b77-4a0e-b62d-a61f2171074d
-- title:
--   BPTCommuting Projector Model: unitary intertwining symm
-- statement:
--   Invert an intertwining equation between unitary coordinate transports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L205-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L205-L220

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

theorem QEC.Bounds.BPTCommutingProjectorModel.unitary_intertwining_symm
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport H K) (W : Semantics.UnitaryTransport H H)
    (V : Semantics.UnitaryTransport K K)
    (hintertwines : T.toLinearEquiv.toLinearMap.comp W.toLinearEquiv.toLinearMap =
      V.toLinearEquiv.toLinearMap.comp T.toLinearEquiv.toLinearMap) :
    W.toLinearEquiv.toLinearMap.comp T.symm.toLinearEquiv.toLinearMap =
      T.symm.toLinearEquiv.toLinearMap.comp V.toLinearEquiv.toLinearMap := by sorry
