-- Prove2me | Theorems.Thm_PI_PhMeasCore_UnitaryGroupMassFormula_smooth_sub
-- name    : PI.PhMeasCore.UnitaryGroupMassFormula.smooth_sub
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:18.739638+00:00
-- url     : https://prove2.me/theorems/65289798-453f-4db1-a796-b1beaf12d3e0
-- title:
--   Unitary Group Mass Formula: smooth sub
-- statement:
--   The Unitary Group Mass Formula construction uses the smooth sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/SmoothTranslate.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SmoothTranslationMeasure/SmoothTranslate.lean#L31-L45

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

theorem PI.PhMeasCore.UnitaryGroupMassFormula.smooth_sub {v v' : H} (hv : v ∈ smoothVecs Hm σ) (hv' : v' ∈ smoothVecs Hm σ) :
    v - v' ∈ smoothVecs Hm σ := by sorry
