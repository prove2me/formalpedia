-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_tm_integral_comp
-- name    : ReciprocityTheory.MultiplicativeHeights.tm_integral_comp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:04:49.362636+00:00
-- url     : https://prove2.me/theorems/0f459313-2c49-50c0-ba06-7e49b012e357
-- title:
--   Multiplicative Heights: tm integral comp
-- statement:
--   The Multiplicative Heights construction uses the tm integral comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanB.lean#L63-L67

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanA
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.MultiplicativeHeights.tm_integral_comp (i : ι) {F : (ι → ℝ) → ℝ} (hF : AEStronglyMeasurable F (torusProb ι)) :
    ∫ θ, F θ ∂(torusProb ι) = ∫ p, F (tmUpd i p) ∂((torusProb ι).prod unitIntervalMeasure) := by sorry
