-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_ts_inG_mul
-- name    : PositivityTheory.Rg.Sw.LVs.ts_inG_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:34.548985+00:00
-- url     : https://prove2.me/theorems/4b215ba3-6a9a-45ad-a081-0b7d1bd3bae9
-- title:
--   LVs: ts in G mul
-- statement:
--   The LVs construction uses the ts in G mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TsContinuousNU.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TsContinuousNU.lean#L14-L18

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

theorem PositivityTheory.Rg.Sw.LVs.ts_inG_mul {g h : M2 n} (hg : InG g) (hh : InG h) : InG (g * h) := by sorry
