-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolB_inG_upper
-- name    : PositivityTheory.Rg.Sw.LVs.HolB.inG_upper
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:26:46.862367+00:00
-- url     : https://prove2.me/theorems/9be252e2-79a1-4f37-b15d-4fbe35997687
-- title:
--   Hol B: in G upper
-- statement:
--   The Hol B construction uses the in G upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/HermRealSmul.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/HermRealSmul.lean#L27-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EventuallyIteratedFDerivEqZeroOfRealSubspace
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HermRealSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology Set Metric Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.HolB.inG_upper {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (fromBlocks 1 b 0 1 : M2 n) := by sorry
