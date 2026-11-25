-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_contDiffOn_hF__e4db1618f210
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_contDiffOn_hF__e4db1618f210
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:10:27.207286+00:00
-- url     : https://prove2.me/theorems/e94ef613-7582-4320-a06d-ce95ac258ccc
-- title:
--   P2 M Positivity Theory Rg Sw LVs cont Diff On h F  e4db1618f210: P2 M Positivity Theory Rg Sw LVs cont Diff On h F  e4db1618f210
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs cont Diff On h F  e4db1618f210 construction uses the P2 M Positivity Theory Rg Sw LVs cont Diff On h F  e4db1618f210 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L113-L116

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

theorem P2M_PositivityTheory_Rg_Sw_LVs_contDiffOn_hF__e4db1618f210 (j : ℕ) (p q : ℤ) : ContDiffOn ℂ ∞ (hF (n := n) j p q) (Dom n) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«contDiffOn_hF'» := P2M_PositivityTheory_Rg_Sw_LVs_contDiffOn_hF__e4db1618f210
