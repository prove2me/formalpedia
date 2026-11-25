-- Prove2me | Theorems.Thm_PI_FJMB_exists_support_of_killS
-- name    : PI.FJMB.exists_support_of_killS
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:31.9458+00:00
-- url     : https://prove2.me/theorems/29b0a817-dd88-50a9-b777-bb27d60a71b1
-- title:
--   FJMB: exists support of kill S
-- statement:
--   The FJMB construction uses the exists support of kill S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurCauchy.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurCauchy.lean#L32-L44

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurDiag
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
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

theorem PI.FJMB.exists_support_of_killS {S : Set σ} {P : MvPolynomial σ ℂ} (h : aeval (killS S) P ≠ 0) :
    ∃ e ∈ P.support, ∀ v ∈ S, e v = 0 := by sorry
