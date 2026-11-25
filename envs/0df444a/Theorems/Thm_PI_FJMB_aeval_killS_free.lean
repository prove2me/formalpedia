-- Prove2me | Theorems.Thm_PI_FJMB_aeval_killS_free
-- name    : PI.FJMB.aeval_killS_free
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:59.749802+00:00
-- url     : https://prove2.me/theorems/c4ced9f6-4745-44ba-8716-c977b765c9cf
-- title:
--   FJMB: aeval kill S free
-- statement:
--   The FJMB construction uses the aeval kill S free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurCauchy.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurCauchy.lean#L46-L56

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

theorem PI.FJMB.aeval_killS_free {S : Set σ} {Q : MvPolynomial σ ℂ} (h : ∀ e ∈ Q.support, ∀ v ∈ S, e v = 0) :
    aeval (killS S) Q = Q := by sorry
