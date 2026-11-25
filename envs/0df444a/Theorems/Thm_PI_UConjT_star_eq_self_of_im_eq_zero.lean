-- Prove2me | Theorems.Thm_PI_UConjT_star_eq_self_of_im_eq_zero
-- name    : PI.UConjT.star_eq_self_of_im_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:19.061127+00:00
-- url     : https://prove2.me/theorems/50ea4fa1-ba18-537c-839b-b8a044c69642
-- title:
--   UConj T: star eq self of im eq zero
-- statement:
--   The UConj T construction uses the star eq self of im eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/SubmatrixMemUnitaryGroup.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryConjugation/SubmatrixMemUnitaryGroup.lean#L11-L12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_SubmatrixMemUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
open Matrix

theorem PI.UConjT.star_eq_self_of_im_eq_zero {z : ℂ} (h : z.im = 0) : star z = z := by sorry
