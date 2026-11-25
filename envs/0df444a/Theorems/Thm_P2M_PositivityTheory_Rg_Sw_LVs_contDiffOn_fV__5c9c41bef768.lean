-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_contDiffOn_fV__5c9c41bef768
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_contDiffOn_fV__5c9c41bef768
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:10:28.71403+00:00
-- url     : https://prove2.me/theorems/bd5fee07-7fb9-4cc9-84a2-eacedad5f2f1
-- title:
--   P2 M Positivity Theory Rg Sw LVs cont Diff On f V  5c9c41bef768: P2 M Positivity Theory Rg Sw LVs cont Diff On f V  5c9c41bef768
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs cont Diff On f V  5c9c41bef768 construction uses the P2 M Positivity Theory Rg Sw LVs cont Diff On f V  5c9c41bef768 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ContDiffOnSecondCayleyBlockEntries.lean#L118-L122

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

theorem P2M_PositivityTheory_Rg_Sw_LVs_contDiffOn_fV__5c9c41bef768 (p q : ℤ) : ContDiffOn ℂ ∞ (fV (n := n) p q) (Dom n) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«contDiffOn_fV'» := P2M_PositivityTheory_Rg_Sw_LVs_contDiffOn_fV__5c9c41bef768
