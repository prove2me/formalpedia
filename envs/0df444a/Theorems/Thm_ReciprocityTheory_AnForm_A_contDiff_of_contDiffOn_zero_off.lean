-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_contDiff_of_contDiffOn_zero_off
-- name    : ReciprocityTheory.AnForm.A.contDiff_of_contDiffOn_zero_off
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:34.424399+00:00
-- url     : https://prove2.me/theorems/642f6d4e-673f-48ec-b666-f6eb07b5c3c9
-- title:
--   A: cont Diff of cont Diff On zero off
-- statement:
--   The A construction uses the cont Diff of cont Diff On zero off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L99-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L99-L108

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

theorem ReciprocityTheory.AnForm.A.contDiff_of_contDiffOn_zero_off {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} {m : WithTop ℕ∞} (hf : ContDiffOn ℝ m f U)
    (h0 : ∀ z ∉ K, f z = 0) : ContDiff ℝ m f := by sorry
