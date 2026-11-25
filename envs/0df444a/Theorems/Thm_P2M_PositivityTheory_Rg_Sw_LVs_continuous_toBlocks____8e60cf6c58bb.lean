-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____8e60cf6c58bb
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____8e60cf6c58bb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:10:37.900589+00:00
-- url     : https://prove2.me/theorems/b042ad6a-0493-4aea-96b0-a27ace1612ed
-- title:
--   P2 M Positivity Theory Rg Sw LVs continuous to Blocks    8e60cf6c58bb: P2 M Positivity Theory Rg Sw LVs continuous to Blocks    8e60cf6c58bb
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs continuous to Blocks    8e60cf6c58bb construction uses the P2 M Positivity Theory Rg Sw LVs continuous to Blocks    8e60cf6c58bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L47-L48

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____8e60cf6c58bb : Continuous (fun x : M2 n => x.toBlocks₁₁) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«continuous_toBlocks₁₁'» := P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____8e60cf6c58bb
