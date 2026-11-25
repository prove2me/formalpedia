-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_contDiffOn_scalar_section
-- name    : PositivityTheory.Rg.Sw.LVs.contDiffOn_scalar_section
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:12.983802+00:00
-- url     : https://prove2.me/theorems/18fc1d14-32f4-4c9e-a403-4e38d08c9d29
-- title:
--   LVs: cont Diff On scalar section
-- statement:
--   The LVs construction uses the cont Diff On scalar section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContinuousOnIteratedFDerivTranslate.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContinuousOnIteratedFDerivTranslate.lean#L37-L38

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

theorem PositivityTheory.Rg.Sw.LVs.contDiffOn_scalar_section (p q : ℤ) : ContDiffOn ℂ ∞ (f0 (n := n) p q) {x | (u1 x).det ≠ 0 ∧ (u2 x).det ≠ 0} := by sorry
