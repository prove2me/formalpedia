-- Prove2me | Theorems.Thm_PI_PhMeasCore_UnitaryGroupMassFormula_smooth_translate
-- name    : PI.PhMeasCore.UnitaryGroupMassFormula.smooth_translate
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:36:03.357802+00:00
-- url     : https://prove2.me/theorems/1f5b934a-4f42-4ff1-91d4-12459273520f
-- title:
--   Unitary Group Mass Formula: smooth translate
-- statement:
--   The Unitary Group Mass Formula construction uses the smooth translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/SmoothTranslate.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/SmoothTranslate.lean#L17-L29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_ContDiffMulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmoothTranslationMeasure_SmoothTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open PI PI.PhMeasCore PI.PhMeasCore.UnitaryGroupMassFormula
open PI.PhMeasCore
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem PI.PhMeasCore.UnitaryGroupMassFormula.smooth_translate {w : H} (hmul : MulOnUH Hm σ) (hw : w ∈ smoothVecs Hm σ)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH Hm) : σ g w ∈ smoothVecs Hm σ := by sorry
