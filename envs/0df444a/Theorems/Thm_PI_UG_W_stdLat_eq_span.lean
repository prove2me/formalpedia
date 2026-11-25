-- Prove2me | Theorems.Thm_PI_UG_W_stdLat_eq_span
-- name    : PI.UG.W.stdLat_eq_span
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:38.487906+00:00
-- url     : https://prove2.me/theorems/cff1b0ba-d640-5359-b4f9-975b3dfcf37e
-- title:
--   W: std Lat eq span
-- statement:
--   The W construction uses the std Lat eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularGenus/StdLatEqSpan.lean#L39-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularGenus/StdLatEqSpan.lean#L39-L57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_StdLatEqSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UG PI.UG.W

theorem PI.UG.W.stdLat_eq_span (E : Type) [Field E] [NumberField E] (n : ℕ) :
    stdLat E n = Submodule.span (𝓞 E) (Set.range (eStd E n)) := by sorry
