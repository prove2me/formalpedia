-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_tsupport_dList_subset
-- name    : PositivityTheory.Rg.Sw.LVs.STD.tsupport_dList_subset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:25.970655+00:00
-- url     : https://prove2.me/theorems/0291325b-b1cf-4582-9dd3-a74f19da9c15
-- title:
--   STD: tsupport d List subset
-- statement:
--   The STD construction uses the tsupport d List subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiffB.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiffB.lean#L51-L54

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

theorem PositivityTheory.Rg.Sw.LVs.STD.tsupport_dList_subset (φ : Vr n → ℂ) : ∀ l : List (Fin n × Fin n), tsupport (dList l φ) ⊆ tsupport φ
  := by sorry
