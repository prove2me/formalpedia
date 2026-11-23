-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_lam_apply
-- name    : PI.UnitaryGroupMassFormula.ChiExCM.lam_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:08.697673+00:00
-- url     : https://prove2.me/theorems/e19c7645-edb5-4e0a-ada0-dde098e79c2e
-- title:
--   Chi Ex CM: lam apply
-- statement:
--   The Chi Ex CM construction uses the lam apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneCharacters/NormOneCharacterApply.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOneCharacters/NormOneCharacterApply.lean#L42-L44

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

theorem PI.UnitaryGroupMassFormula.ChiExCM.lam_apply (c : E →+* E) (S : Type) [Fintype S] (emb : S → E →+* ℂ) (u : normOne c) :
    ((lam c S emb u : ℂˣ) : ℂ) = ∏ s, (emb s ((u : Eˣ) : E))⁻¹ := by sorry
