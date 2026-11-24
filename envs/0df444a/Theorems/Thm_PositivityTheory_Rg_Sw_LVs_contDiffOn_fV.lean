-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiffOn_fV
-- name    : PositivityTheory.Rg.Sw.LVs.contDiffOn_fV
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:52.528916+00:00
-- url     : https://prove2.me/theorems/80edb6a0-c344-48b4-9847-ab9b7c574c48
-- title:
--   LVs: cont Diff On f V
-- statement:
--   The LVs construction uses the cont Diff On f V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContinuousOnIteratedFDerivTranslate.lean#L42-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContinuousOnIteratedFDerivTranslate.lean#L42-L42

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.contDiffOn_fV (p q : ℤ) : ContDiffOn ℂ ∞ (fV (n := n) p q) (Dom n) := by sorry
