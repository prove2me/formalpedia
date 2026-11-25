-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_normOne_character_apply
-- name    : PI.UnitaryGroupMassFormula.ChiExCM.normOne_character_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:16.576584+00:00
-- url     : https://prove2.me/theorems/3ad41644-77b6-4925-bed9-901d9c4670ae
-- title:
--   Chi Ex CM: norm One character apply
-- statement:
--   The Chi Ex CM construction uses the norm One character apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneCharacters/NormOneCharacterApply.lean#L80-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneCharacters/NormOneCharacterApply.lean#L80-L87

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

theorem PI.UnitaryGroupMassFormula.ChiExCM.normOne_character_apply (c : E →+* E) (S : Type) [Fintype S] (emb : S → E →+* ℂ)
    (hker : (iota c).ker ≤ (lam c S emb).ker) (u : normOne c) :
    chi0 c S emb hker ⟨iota c u, MonoidHom.mem_range.2 ⟨u, rfl⟩⟩ = lam c S emb u := by sorry
