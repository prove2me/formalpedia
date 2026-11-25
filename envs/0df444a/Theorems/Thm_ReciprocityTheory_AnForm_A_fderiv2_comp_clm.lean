-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_comp_clm
-- name    : ReciprocityTheory.AnForm.A.fderiv2_comp_clm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:51:21.420724+00:00
-- url     : https://prove2.me/theorems/fb52184c-8013-499b-a14e-f79353a9c840
-- title:
--   A: fderiv2 comp clm
-- statement:
--   The A construction uses the fderiv2 comp clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L13-L24

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenOfPoincareLelongHyperplane
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_HessCRestrictThm
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContDiffOfContDiffOnZeroOff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section

theorem ReciprocityTheory.AnForm.A.fderiv2_comp_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → ℝ) (P : F →L[ℝ] E) (hg : ContDiff ℝ 2 g)
    (z a b : F) :
    fderiv ℝ (fderiv ℝ (g ∘ P)) z a b = fderiv ℝ (fderiv ℝ g) (P z) (P a) (P b) := by sorry
