-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_max_one_le
-- name    : PI.UnitaryGroupMassFormula.UsCost.max_one_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:03.155415+00:00
-- url     : https://prove2.me/theorems/1b46a6b6-10fb-5993-9cb8-76b72677ab37
-- title:
--   Us Cost: max one le
-- statement:
--   The Us Cost construction uses the max one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterC.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ZIterC.lean#L22-L26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost

theorem PI.UnitaryGroupMassFormula.UsCost.max_one_le (c t : ℝ) (ht : 1 ≤ t) (x : ℝ) (hx : x ≤ c * t) : max 1 x ≤ (1 + |c|) * t := by sorry
