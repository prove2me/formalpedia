-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__f3b15b56784f
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__f3b15b56784f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:11:11.557649+00:00
-- url     : https://prove2.me/theorems/bf74d80c-1b58-4852-875d-f94b84f2310a
-- title:
--   P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  f3b15b56784f: P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  f3b15b56784f
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  f3b15b56784f construction uses the P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  f3b15b56784f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L89-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L89-L89

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_InfInvA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivXZxSkew
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.II
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__f3b15b56784f (M : M2 n) (a b : Fin n) : M.toBlocks₁₁ a b = M (Sum.inl a) (Sum.inl b) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«II».«toBlocks₁₁_apply'» := P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__f3b15b56784f
