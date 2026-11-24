-- Prove2me | Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_tT_mem
-- name    : PI.ScPsiExists.UnitaryGroupMassFormula.tT_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:57:09.853981+00:00
-- url     : https://prove2.me/theorems/6d8f1fd9-16d2-4aea-b7a6-09fe9931d114
-- title:
--   Unitary Group Mass Formula: t T mem
-- statement:
--   The Unitary Group Mass Formula construction uses the t T mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EmbeddingTraceSumAlt/NormUnitsOfCalculation.lean#L113-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EmbeddingTraceSumAlt/NormUnitsOfCalculation.lean#L113-L154

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem PI.ScPsiExists.UnitaryGroupMassFormula.tT_mem (τ : E →ₗ[F] F)
    (hτ : ∀ c : 𝓞 E, ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = τ (algebraMap (𝓞 E) E c))
    (z : E ⊗[F] Af F) (hz : z ∈ IntAf F E) : tT τ z ∈ Formalism.UG.intAd F := by sorry
