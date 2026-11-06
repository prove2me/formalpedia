-- Prove2me | Theorems.Thm_QEC_Semantics_JumpProtected_jump_mul_observable_projector
-- name    : QEC.Semantics.JumpProtected.jump_mul_observable_projector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:59:27.460448+00:00
-- url     : https://prove2.me/theorems/551124d3-80d8-4052-96ea-836ef9aa0ad0
-- title:
--   Jump Protected: jump mul observable projector
-- statement:
--   The Jump Protected construction uses the jump mul observable projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L147-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L147-L152

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]

theorem QEC.Semantics.JumpProtected.jump_mul_observable_projector [Fintype ι]
    {J : ι → Operator H} {O P : Operator H} (h : JumpProtected J O P) (a : ι) :
    J a * O * P = O * J a * P := by sorry
