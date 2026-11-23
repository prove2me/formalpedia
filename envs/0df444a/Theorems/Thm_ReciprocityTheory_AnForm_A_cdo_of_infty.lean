-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_cdo_of_infty
-- name    : ReciprocityTheory.AnForm.A.cdo_of_infty
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:42.051928+00:00
-- url     : https://prove2.me/theorems/149a766a-7753-40f2-8df9-27e222660752
-- title:
--   A: cdo of infty
-- statement:
--   The A construction uses the cdo of infty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L270-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L270-L272

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
variable {n : ℕ}

theorem ReciprocityTheory.AnForm.A.cdo_of_infty {D : ℕ} {f : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)}
    (h : ContDiffOn ℝ ∞ f U) (m : ℕ) : ContDiffOn ℝ (m + 2) f U := by sorry
