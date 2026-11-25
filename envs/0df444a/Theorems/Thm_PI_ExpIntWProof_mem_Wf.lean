-- Prove2me | Theorems.Thm_PI_ExpIntWProof_mem_Wf
-- name    : PI.ExpIntWProof.mem_Wf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:54:00.169498+00:00
-- url     : https://prove2.me/theorems/07ec0e88-e52d-5b18-99bb-3ad8e12e1775
-- title:
--   Exp Int WProof: mem Wf
-- statement:
--   The Exp Int WProof construction uses the mem Wf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatMemWf.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatMemWf.lean#L31-L31

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof
open PI

theorem PI.ExpIntWProof.mem_Wf {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} : x ∈ Wf p ↔ InWf x := by sorry
