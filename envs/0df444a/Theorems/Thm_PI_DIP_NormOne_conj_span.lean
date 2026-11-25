-- Prove2me | Theorems.Thm_PI_DIP_NormOne_conj_span
-- name    : PI.DIP.NormOne.conj_span
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:27:05.500065+00:00
-- url     : https://prove2.me/theorems/30a3ba4a-c3d5-4514-bdc4-1a8d2a7bc33e
-- title:
--   Norm One: conj span
-- statement:
--   The Norm One construction uses the conj span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/NormOne.lean#L62-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/NormOne.lean#L62-L78

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

theorem PI.DIP.NormOne.conj_span (c : E →+* E) (hc : ∀ x, c (c x) = x) {B : Submodule (𝓞 E) E} (a : E)
    (hB : ∀ x, x ∈ B ↔ c x ∈ Submodule.span (𝓞 E) {a}) :
    B = Submodule.span (𝓞 E) {c a} := by sorry
