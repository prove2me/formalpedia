-- Prove2me | Theorems.Thm_PI_DIP_NormOne_pow_principal
-- name    : PI.DIP.NormOne.pow_principal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:26:36.156631+00:00
-- url     : https://prove2.me/theorems/185eb1b9-f295-5d62-888b-45c2a10b4f96
-- title:
--   Norm One: pow principal
-- statement:
--   The Norm One construction uses the pow principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/NormOne.lean#L80-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/NormOne.lean#L80-L104

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

theorem PI.DIP.NormOne.pow_principal {𝔞 𝔟 : Submodule (𝓞 E) E} (hab : 𝔞 * 𝔟 = 1) :
    ∃ (h : ℕ) (a : E), 0 < h ∧ 𝔞 ^ h = Submodule.span (𝓞 E) {a} := by sorry
