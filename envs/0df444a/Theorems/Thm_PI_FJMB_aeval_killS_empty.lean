-- Prove2me | Theorems.Thm_PI_FJMB_aeval_killS_empty
-- name    : PI.FJMB.aeval_killS_empty
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:32:20.909566+00:00
-- url     : https://prove2.me/theorems/f8cf3857-cf5c-54a8-a582-d0fecda332fa
-- title:
--   FJMB: aeval kill S empty
-- statement:
--   The FJMB construction uses the aeval kill S empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L28-L30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}

theorem PI.FJMB.aeval_killS_empty (f : MvPolynomial σ ℂ) : aeval (killS (∅ : Set σ)) f = f := by sorry
