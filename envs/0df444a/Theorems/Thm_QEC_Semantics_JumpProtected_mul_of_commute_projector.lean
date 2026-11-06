-- Prove2me | Theorems.Thm_QEC_Semantics_JumpProtected_mul_of_commute_projector
-- name    : QEC.Semantics.JumpProtected.mul_of_commute_projector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:46.090049+00:00
-- url     : https://prove2.me/theorems/a5615c2a-c541-437f-9388-cdcfd5f20c05
-- title:
--   Jump Protected: mul of commute projector
-- statement:
--   The Jump Protected construction uses the mul of commute projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ProtectedObservableDecay.lean#L431-L452
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/ProtectedObservableDecay.lean#L431-L452

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

theorem QEC.Semantics.JumpProtected.mul_of_commute_projector [Fintype ι]
    {J : ι → Operator H} {O₁ O₂ P : Operator H}
    (h₁ : JumpProtected J O₁ P) (h₂ : JumpProtected J O₂ P)
    (h₂P : Commute O₂ P) :
    JumpProtected J (O₁ * O₂) P := by sorry
