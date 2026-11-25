-- Prove2me | Theorems.Thm_PI_LowSplitHaarW_measurePreserving_of_card
-- name    : PI.LowSplitHaarW.measurePreserving_of_card
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:34.744631+00:00
-- url     : https://prove2.me/theorems/b106ea92-76f1-48e2-8b8d-7b2726e03a8f
-- title:
--   Low Split Haar W: measure Preserving of card
-- statement:
--   The Low Split Haar W construction uses the measure Preserving of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerShearHaar/MeasurePreservingOfCard.lean#L21-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerShearHaar/MeasurePreservingOfCard.lean#L21-L79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_MeasurePreservingOfCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.LowSplitHaarW

theorem PI.LowSplitHaarW.measurePreserving_of_card (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (r : ι → ℕ) (g : ι → (ι → ℂ) → ℂ), (∀ i, Measurable (g i)) →
    (∀ i (x y : ι → ℂ), (∀ j, r j < r i → x j = y j) → g i x = g i y) →
    MeasurePreserving (fun x : ι → ℂ => fun i => x i + g i x) volume volume := by sorry
