-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_iota_val
-- name    : PI.UnitaryGroupMassFormula.ChiExCM.iota_val
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:33.202681+00:00
-- url     : https://prove2.me/theorems/257c1d03-24e9-568a-b332-7d6b84c434b5
-- title:
--   Chi Ex CM: iota val
-- statement:
--   The Chi Ex CM construction uses the iota val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneCharacters/NormOneCharacterApply.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneCharacters/NormOneCharacterApply.lean#L36-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ChiExCM
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharExtend
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOneCharacters_NormOneCharacterApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ChiExCM
open NumberField
variable {E : Type} [Field E] [NumberField E]

theorem PI.UnitaryGroupMassFormula.ChiExCM.iota_val (c : E →+* E) (u : normOne c) :
    ((iota c u : (Submodule (𝓞 E) E)ˣ) : Submodule (𝓞 E) E) = Submodule.span (𝓞 E) {((u : Eˣ) : E)} := by sorry
