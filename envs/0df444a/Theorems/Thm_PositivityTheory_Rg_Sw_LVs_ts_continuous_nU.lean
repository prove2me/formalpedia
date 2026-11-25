-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_ts_continuous_nU
-- name    : PositivityTheory.Rg.Sw.LVs.ts_continuous_nU
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:01:04.598483+00:00
-- url     : https://prove2.me/theorems/200d1a98-a4c2-5bbb-89f5-f16fc8a170e8
-- title:
--   LVs: ts continuous n U
-- statement:
--   The LVs construction uses the ts continuous n U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TsContinuousNU.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TsContinuousNU.lean#L34-L36

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

theorem PositivityTheory.Rg.Sw.LVs.ts_continuous_nU : Continuous (nU : Matrix (Fin n) (Fin n) ℂ → M2 n) := by sorry
