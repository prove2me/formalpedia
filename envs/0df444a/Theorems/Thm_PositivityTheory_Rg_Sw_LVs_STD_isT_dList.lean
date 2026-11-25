-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_STD_isT_dList
-- name    : PositivityTheory.Rg.Sw.LVs.STD.isT_dList
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:02.571091+00:00
-- url     : https://prove2.me/theorems/4bf68f8b-72c0-48ff-8a74-ce045ecb08a4
-- title:
--   STD: is T d List
-- statement:
--   The STD construction uses the is T d List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiffB.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiffB.lean#L47-L49

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

theorem PositivityTheory.Rg.Sw.LVs.STD.isT_dList {U : Set (Vr n)} {φ : Vr n → ℂ} (h : IsT U φ) : ∀ l : List (Fin n × Fin n), IsT U (dList l φ)
  := by sorry
