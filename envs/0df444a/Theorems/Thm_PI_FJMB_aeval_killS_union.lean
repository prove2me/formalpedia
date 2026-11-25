-- Prove2me | Theorems.Thm_PI_FJMB_aeval_killS_union
-- name    : PI.FJMB.aeval_killS_union
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:30:06.165721+00:00
-- url     : https://prove2.me/theorems/8cff3dbf-bd6e-4868-a2e8-9e98f1ef6f0e
-- title:
--   FJMB: aeval kill S union
-- statement:
--   The FJMB construction uses the aeval kill S union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurElim.lean#L32-L39

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

theorem PI.FJMB.aeval_killS_union (S T : Set σ) (f : MvPolynomial σ ℂ) :
    aeval (killS S) (aeval (killS T) f) = aeval (killS (S ∪ T)) f := by sorry
