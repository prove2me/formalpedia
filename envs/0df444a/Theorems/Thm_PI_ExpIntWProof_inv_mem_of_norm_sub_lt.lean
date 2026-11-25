-- Prove2me | Theorems.Thm_PI_ExpIntWProof_inv_mem_of_norm_sub_lt
-- name    : PI.ExpIntWProof.inv_mem_of_norm_sub_lt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:53.714241+00:00
-- url     : https://prove2.me/theorems/aac86b27-84ec-4842-b4ca-892064fda049
-- title:
--   Exp Int WProof: inv mem of norm sub lt
-- statement:
--   The Exp Int WProof construction uses the inv mem of norm sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatCastMemWittIntegers.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatCastMemWittIntegers.lean#L22-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatCastMemWittIntegers
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

theorem PI.ExpIntWProof.inv_mem_of_norm_sub_lt (p : ℕ) [Fact p.Prime] {x : ℂ_[p]} (hx : x ∈ Wp p)
    (h : ‖1 - x‖ < 1) : x⁻¹ ∈ Wp p := by sorry
