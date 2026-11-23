-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_contDiffOn
-- name    : ReciprocityTheory.AnForm.A.mdisc_contDiffOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:58:14.232198+00:00
-- url     : https://prove2.me/theorems/207478d6-b5a4-480d-8770-7c0dfab9bd4d
-- title:
--   A: mdisc cont Diff On
-- statement:
--   The A construction uses the mdisc cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L132-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L132-L139

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

theorem ReciprocityTheory.AnForm.A.mdisc_contDiffOn {D : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin D → E → Matrix (Fin D) (Fin D) ℂ) {s : Set E} {m : WithTop ℕ∞}
    (hA : ∀ k i j, ContDiffOn ℝ m (fun z => A k z i j) s) :
    ContDiffOn ℝ m (fun z => mdisc (fun k => A k z)) s := by sorry
