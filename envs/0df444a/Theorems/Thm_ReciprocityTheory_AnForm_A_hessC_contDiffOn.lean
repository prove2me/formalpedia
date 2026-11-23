-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_hessC_contDiffOn
-- name    : ReciprocityTheory.AnForm.A.hessC_contDiffOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:09.760494+00:00
-- url     : https://prove2.me/theorems/e44d3ec7-8921-4082-85ca-8be82e91022f
-- title:
--   A: hess C cont Diff On
-- statement:
--   The A construction uses the hess C cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L119-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L119-L130

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

theorem ReciprocityTheory.AnForm.A.hessC_contDiffOn {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {m : ℕ} (hφ : ContDiffOn ℝ (m + 2) φ U) (i j : Fin D) :
    ContDiffOn ℝ m (fun z => hessC φ z i j) U := by sorry
