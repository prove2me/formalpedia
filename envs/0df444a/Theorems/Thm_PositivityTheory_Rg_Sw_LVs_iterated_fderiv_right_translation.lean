-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_iterated_fderiv_right_translation
-- name    : PositivityTheory.Rg.Sw.LVs.iterated_fderiv_right_translation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:33.911436+00:00
-- url     : https://prove2.me/theorems/22cfedd0-df69-4806-8987-acc69958c928
-- title:
--   LVs: iterated fderiv right translation
-- statement:
--   The LVs construction uses the iterated fderiv right translation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFderivRightTranslation.lean#L28-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFderivRightTranslation.lean#L28-L48

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

theorem PositivityTheory.Rg.Sw.LVs.iterated_fderiv_right_translation {N : ℕ} (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    (W : Fin (N + 1) → M2 n) (hW : ∀ a b, W a * W b = 0) (x : M2 n) (hx : x ∈ U) :
    fderiv ℂ (fun y => iteratedFDeriv ℂ N F y (fun i => y * W i.succ)) x (x * W 0) =
      iteratedFDeriv ℂ (N + 1) F x (fun i => x * W i) := by sorry
