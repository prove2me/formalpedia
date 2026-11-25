-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_mem_normOne
-- name    : PI.UnitaryGroupMassFormula.ChiExCM.mem_normOne
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:17.388134+00:00
-- url     : https://prove2.me/theorems/b7922daa-abeb-43dd-b89f-12c375d9a686
-- title:
--   Chi Ex CM: mem norm One
-- statement:
--   The Chi Ex CM construction uses the mem norm One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneCharacters/NormOneCharacterApply.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneCharacters/NormOneCharacterApply.lean#L31-L31

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

theorem PI.UnitaryGroupMassFormula.ChiExCM.mem_normOne (c : E →+* E) (u : Eˣ) : u ∈ normOne c ↔ (u : E) * c u = 1 := by sorry
