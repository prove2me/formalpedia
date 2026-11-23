-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_contDiffOn_re__3be3b0114f88
-- name    : P2M_ReciprocityTheory_AnForm_A_contDiffOn_re__3be3b0114f88
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:02.062277+00:00
-- url     : https://prove2.me/theorems/16b713a8-c709-40e5-bcc4-3d62913dfd6c
-- title:
--   P2 M Reciprocity Theory An Form A cont Diff On re  3be3b0114f88: P2 M Reciprocity Theory An Form A cont Diff On re  3be3b0114f88
-- statement:
--   The P2 M Reciprocity Theory An Form A cont Diff On re  3be3b0114f88 construction uses the P2 M Reciprocity Theory An Form A cont Diff On re  3be3b0114f88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L279-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContDiffOfContDiffOnZeroOff.lean#L279-L282

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

theorem P2M_ReciprocityTheory_AnForm_A_contDiffOn_re__3be3b0114f88 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℂ}
    {s : Set E} {m : WithTop ℕ∞} (h : ContDiffOn ℝ m g s) :
    ContDiffOn ℝ m (fun z => (g z).re) s := by sorry

alias «ReciprocityTheory».«AnForm».«A».«contDiffOn_re'» := P2M_ReciprocityTheory_AnForm_A_contDiffOn_re__3be3b0114f88
