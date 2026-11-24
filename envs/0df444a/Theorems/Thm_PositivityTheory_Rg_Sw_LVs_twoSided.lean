-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_twoSided
-- name    : PositivityTheory.Rg.Sw.LVs.twoSided
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:17.045132+00:00
-- url     : https://prove2.me/theorems/9bdaa5e5-0f7d-4595-ba9d-83e0b40ac053
-- title:
--   LVs: two Sided
-- statement:
--   The LVs construction uses the two Sided property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TsContinuousNU.lean#L39-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TsContinuousNU.lean#L39-L94

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_IsSingTest
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TsContinuousNU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
variable {n : ℕ}
set_option maxHeartbeats 1000000

theorem PositivityTheory.Rg.Sw.LVs.twoSided : TwoSided := by sorry
