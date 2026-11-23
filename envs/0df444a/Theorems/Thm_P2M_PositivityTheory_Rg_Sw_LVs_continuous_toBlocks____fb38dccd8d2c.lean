-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____fb38dccd8d2c
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____fb38dccd8d2c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:48.900835+00:00
-- url     : https://prove2.me/theorems/cb5e3d05-038d-4f80-8afd-c43470194221
-- title:
--   P2 M Positivity Theory Rg Sw LVs continuous to Blocks    fb38dccd8d2c: P2 M Positivity Theory Rg Sw LVs continuous to Blocks    fb38dccd8d2c
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs continuous to Blocks    fb38dccd8d2c construction uses the P2 M Positivity Theory Rg Sw LVs continuous to Blocks    fb38dccd8d2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L41-L42

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

theorem P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____fb38dccd8d2c : Continuous (fun x : M2 n => x.toBlocks₂₁) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«continuous_toBlocks₂₁'» := P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____fb38dccd8d2c
