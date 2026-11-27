-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__ee603a23b9dc
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__ee603a23b9dc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:55.545959+00:00
-- url     : https://prove2.me/theorems/600e8ad8-d537-5297-8e10-03905e1c98bd
-- title:
--   P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  ee603a23b9dc: P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  ee603a23b9dc
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  ee603a23b9dc construction uses the P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  ee603a23b9dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L88-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L88-L88

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

theorem P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__ee603a23b9dc (M : M2 n) (a b : Fin n) : M.toBlocks₂₁ a b = M (Sum.inr a) (Sum.inl b) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«II».«toBlocks₂₁_apply'» := P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__ee603a23b9dc
