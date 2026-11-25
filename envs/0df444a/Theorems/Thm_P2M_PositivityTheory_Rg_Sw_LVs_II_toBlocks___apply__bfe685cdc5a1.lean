-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__bfe685cdc5a1
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__bfe685cdc5a1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:10:34.847549+00:00
-- url     : https://prove2.me/theorems/9a91efd4-cd55-417e-a1b5-9c86a913371d
-- title:
--   P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  bfe685cdc5a1: P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  bfe685cdc5a1
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  bfe685cdc5a1 construction uses the P2 M Positivity Theory Rg Sw LVs II to Blocks   apply  bfe685cdc5a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L87-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/FderivXZxSkew.lean#L87-L87

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

theorem P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__bfe685cdc5a1 (M : M2 n) (a b : Fin n) : M.toBlocks₂₂ a b = M (Sum.inr a) (Sum.inr b) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«II».«toBlocks₂₂_apply'» := P2M_PositivityTheory_Rg_Sw_LVs_II_toBlocks___apply__bfe685cdc5a1
