-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_ker_le
-- name    : PI.UnitaryGroupMassFormula.ChiExCM.ker_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:59.266139+00:00
-- url     : https://prove2.me/theorems/e9fe83a4-ab14-48ec-86a7-94ebeb17ee9d
-- title:
--   Chi Ex CM: ker le
-- statement:
--   The Chi Ex CM construction uses the ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneCharacters/NormOneCharacterApply.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneCharacters/NormOneCharacterApply.lean#L65-L73

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

theorem PI.UnitaryGroupMassFormula.ChiExCM.ker_le (c : E →+* E) (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x))
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (hμ : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ s, emb s x = 1) :
    (iota c).ker ≤ (lam c S emb).ker := by sorry
