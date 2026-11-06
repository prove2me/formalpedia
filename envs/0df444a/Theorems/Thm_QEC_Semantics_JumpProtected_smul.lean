-- Prove2me | Theorems.Thm_QEC_Semantics_JumpProtected_smul
-- name    : QEC.Semantics.JumpProtected.smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:44.202554+00:00
-- url     : https://prove2.me/theorems/358d0dfa-0197-4603-8a53-051671e9b322
-- title:
--   Jump Protected: smul
-- statement:
--   The Jump Protected construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ProtectedObservableDecay.lean#L419-L429
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ProtectedObservableDecay.lean#L419-L429

import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_ProtectedObservableDecay
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped ComplexOrder
noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
attribute [local instance] QEC.Semantics.clbtFiniteQuantumSystemComplete

theorem QEC.Semantics.JumpProtected.smul [Fintype ι]
    {J : ι → Operator H} {O P : Operator H}
    (h : JumpProtected J O P) (c : ℂ) :
    JumpProtected J (c • O) P := by sorry
