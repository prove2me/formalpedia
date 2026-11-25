-- Prove2me | Theorems.Thm_PI_WfEndProof_coprime_sq_sub_one
-- name    : PI.WfEndProof.coprime_sq_sub_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:07.566902+00:00
-- url     : https://prove2.me/theorems/96d63f4b-ef5c-574b-aa3c-c82a2c1d5319
-- title:
--   Wf End Proof: coprime sq sub one
-- statement:
--   The Wf End Proof construction uses the coprime sq sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittEndomorphism/FlogConstantCoeff.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WittEndomorphism/FlogConstantCoeff.lean#L40-L50

import Definitions.Def_Formalism_PeriodIntegrals_W2pair
import Definitions.Def_Formalism_PeriodIntegrals_WfRing
import Definitions.Def_Formalism_PeriodIntegrals_WfSubst
import Definitions.Def_Formalism_PeriodIntegrals_InvSerSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_StepIII
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittEndomorphism_FlogConstantCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfEndProof
open PI

theorem PI.WfEndProof.coprime_sq_sub_one (p : ℕ) [hp : Fact p.Prime] : Nat.Coprime (p ^ 2 - 1) p := by sorry
