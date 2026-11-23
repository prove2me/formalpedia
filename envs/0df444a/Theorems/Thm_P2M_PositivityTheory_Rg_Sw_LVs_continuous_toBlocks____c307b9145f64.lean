-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____c307b9145f64
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____c307b9145f64
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:05.323516+00:00
-- url     : https://prove2.me/theorems/ea349fe5-72cd-4a21-bb0a-e9f62b71fa8e
-- title:
--   P2 M Positivity Theory Rg Sw LVs continuous to Blocks    c307b9145f64: P2 M Positivity Theory Rg Sw LVs continuous to Blocks    c307b9145f64
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs continuous to Blocks    c307b9145f64 construction uses the P2 M Positivity Theory Rg Sw LVs continuous to Blocks    c307b9145f64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/ScalarSectionCompactBlockInvariant.lean#L44-L45

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

theorem P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____c307b9145f64 : Continuous (fun x : M2 n => x.toBlocks₂₂) := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«continuous_toBlocks₂₂'» := P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____c307b9145f64
