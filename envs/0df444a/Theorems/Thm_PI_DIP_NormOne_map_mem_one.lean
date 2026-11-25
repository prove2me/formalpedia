-- Prove2me | Theorems.Thm_PI_DIP_NormOne_map_mem_one
-- name    : PI.DIP.NormOne.map_mem_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:26:44.912204+00:00
-- url     : https://prove2.me/theorems/f0cd4191-9307-58c5-ab65-101560f52f7e
-- title:
--   Norm One: map mem one
-- statement:
--   The Norm One construction uses the map mem one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/NormOne.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/NormOne.lean#L41-L44

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DetIdPG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_StNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_NormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open PI PI.DIP PI.DIP.NormOne
variable {E : Type} [Field E] [NumberField E]

theorem PI.DIP.NormOne.map_mem_one (c : E →+* E) : ∀ x ∈ (1 : Submodule (𝓞 E) E), c x ∈ (1 : Submodule (𝓞 E) E) := by sorry
