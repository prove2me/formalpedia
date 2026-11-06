-- Prove2me | Theorems.Thm_QEC_Semantics_KnillLaflamme_unitaryTransport_iff
-- name    : QEC.Semantics.KnillLaflamme.unitaryTransport_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:38:53.633213+00:00
-- url     : https://prove2.me/theorems/85dbf957-c80a-4f0a-82eb-8db836425ef9
-- title:
--   Knill Laflamme: unitary Transport iff
-- statement:
--   The selected Knill-Laflamme matrix-element criterion is invariant under unitary
--   transport of the code and conjugation of the error family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KnillLaflamme.lean#L218-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KnillLaflamme.lean#L218-L226

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

theorem QEC.Semantics.KnillLaflamme.unitaryTransport_iff
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {errors : Set (Operator H)}
    (hCD : QuantumCode.TransportedBy U C D) :
    KnillLaflammeCriterion H C errors ↔
      KnillLaflammeCriterion K D (Set.image (UnitaryTransport.conjOperator U) errors) := by sorry
