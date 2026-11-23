-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cont_on_K
-- name    : PositivityTheory.Rg.Sw.LVs.cont_on_K
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:08.731122+00:00
-- url     : https://prove2.me/theorems/5b7af234-fd7b-484f-8ad4-2d898705bc78
-- title:
--   LVs: cont on K
-- statement:
--   The LVs construction uses the cont on K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFderivRightTranslation.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFderivRightTranslation.lean#L148-L150

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.cont_on_K (H : M2 n → ℂ) (hH : ContDiffOn ℂ ∞ H (Dom n)) (Kg : Type) [TopologicalSpace Kg]
    (ι : Kg → M2 n) (hι : Continuous ι) (hdom : ∀ k, ι k ∈ Dom n) : Continuous (fun k => H (ι k)) := by sorry
