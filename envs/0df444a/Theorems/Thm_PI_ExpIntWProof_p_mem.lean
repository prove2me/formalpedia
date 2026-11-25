-- Prove2me | Theorems.Thm_PI_ExpIntWProof_p_mem
-- name    : PI.ExpIntWProof.p_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:50.428586+00:00
-- url     : https://prove2.me/theorems/232e51c9-a203-4ca5-b5cb-879568ae00be
-- title:
--   Exp Int WProof: p mem
-- statement:
--   The Exp Int WProof construction uses the p mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatCastMemWittIntegers.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialIntegrality/InvNatCastMemWittIntegers.lean#L20-L20

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

theorem PI.ExpIntWProof.p_mem (p : ℕ) [Fact p.Prime] : (p : ℂ_[p]) ∈ Wp p := by sorry
