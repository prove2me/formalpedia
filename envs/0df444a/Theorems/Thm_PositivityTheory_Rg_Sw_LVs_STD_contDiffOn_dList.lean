-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_contDiffOn_dList
-- name    : PositivityTheory.Rg.Sw.LVs.STD.contDiffOn_dList
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:49:58.488686+00:00
-- url     : https://prove2.me/theorems/71fc3fee-b4c7-457f-9c7b-e97de18707cc
-- title:
--   STD: cont Diff On d List
-- statement:
--   The STD construction uses the cont Diff On d List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiffB.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiffB.lean#L22-L25

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw.LVs.STD
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.STD.contDiffOn_dList {U : Set (Vr n)} (hU : IsOpen U) {f : Vr n → ℂ} (hf : ContDiffOn ℝ ∞ f U) :
    ∀ l : List (Fin n × Fin n), ContDiffOn ℝ ∞ (dList l f) U
  := by sorry
