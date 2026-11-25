-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_cdo_id
-- name    : PositivityTheory.Rg.Sw.LVs.cdo_id
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:27.146729+00:00
-- url     : https://prove2.me/theorems/6382d6c6-83e3-515b-82b5-6aa97aa42d31
-- title:
--   LVs: cdo id
-- statement:
--   The LVs construction uses the cdo id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L83-L84

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
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
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PositivityTheory.Rg.Sw.LVs.cdo_id (s : Set (M2 n)) : ∀ i j, ContDiffOn ℂ ∞ (fun x : M2 n => x i j) s := by sorry
