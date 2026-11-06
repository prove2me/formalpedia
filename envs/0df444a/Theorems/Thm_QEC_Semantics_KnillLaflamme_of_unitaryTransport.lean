-- Prove2me | Theorems.Thm_QEC_Semantics_KnillLaflamme_of_unitaryTransport
-- name    : QEC.Semantics.KnillLaflamme.of_unitaryTransport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:05:30.228193+00:00
-- url     : https://prove2.me/theorems/44cd8f18-1116-4ada-ad3e-9a37faa14524
-- title:
--   Knill Laflamme: of unitary Transport
-- statement:
--   Pull the transported Knill-Laflamme criterion back along a unitary equivalence
--   of code carriers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KnillLaflamme.lean#L190-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KnillLaflamme.lean#L190-L212

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

theorem QEC.Semantics.KnillLaflamme.of_unitaryTransport
    (U : UnitaryTransport H K) {C : QuantumCode H} {D : QuantumCode K}
    {errors : Set (Operator H)}
    (hCD : QuantumCode.TransportedBy U C D)
    (hKL : KnillLaflammeCriterion K D (Set.image (UnitaryTransport.conjOperator U) errors)) :
    KnillLaflammeCriterion H C errors := by sorry
