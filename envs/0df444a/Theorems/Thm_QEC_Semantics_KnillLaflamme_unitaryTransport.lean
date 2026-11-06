-- Prove2me | Theorems.Thm_QEC_Semantics_KnillLaflamme_unitaryTransport
-- name    : QEC.Semantics.KnillLaflamme.unitaryTransport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:05:13.484446+00:00
-- url     : https://prove2.me/theorems/a29c0a26-48be-4695-8ef0-32931d7558ed
-- title:
--   Knill Laflamme: unitary Transport
-- statement:
--   Transport the selected Knill-Laflamme matrix-element criterion across a unitary
--   equivalence of code carriers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KnillLaflamme.lean#L138-L184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KnillLaflamme.lean#L138-L184

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
noncomputable section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
open QEC.Semantics.KnillLaflamme
variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

theorem QEC.Semantics.KnillLaflamme.unitaryTransport
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {errors : Set (Operator H)}
    (hCD : QuantumCode.TransportedBy U C D)
    (hKL : KnillLaflammeCriterion H C errors) :
    KnillLaflammeCriterion K D (Set.image (UnitaryTransport.conjOperator U) errors) := by sorry
