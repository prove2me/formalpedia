-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_conj_isometric_lift
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_isometric_lift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:09:10.18119+00:00
-- url     : https://prove2.me/theorems/cd1a8e61-00d6-409f-a2ab-a03a90e8015e
-- title:
--   BPTCommuting Projector Model: unitary Transport conj isometric lift
-- statement:
--   Transporting an isometric lift through a unitary transports its embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L274-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Assembly/AssemblyHelpers.lean#L274-L286

import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
noncomputable section
open QEC
universe u

theorem QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_isometric_lift
    {S H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport H K) (J : S →ₗ[Complex] H)
    (P : Semantics.Operator S) :
    T.conjOperator (J.comp (P.comp (LinearMap.adjoint J))) =
      (T.toLinearEquiv.toLinearMap.comp J).comp
        (P.comp (LinearMap.adjoint (T.toLinearEquiv.toLinearMap.comp J))) := by sorry
