-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_blocks_of_InG
-- name    : PositivityTheory.Rg.Sw.LVs.blocks_of_InG
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:03.750405+00:00
-- url     : https://prove2.me/theorems/0f7c4128-8d91-4de8-93bd-33cad3cfa40a
-- title:
--   LVs: blocks of In G
-- statement:
--   The LVs construction uses the blocks of In G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L174-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L174-L188

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.blocks_of_InG {x : M2 n} (hx : InG x) :
    x.toBlocks₂₁ * (x.toBlocks₂₂)ᴴ = x.toBlocks₂₂ * (x.toBlocks₂₁)ᴴ ∧
      x.toBlocks₂₂ * (x.toBlocks₁₁)ᴴ - x.toBlocks₂₁ * (x.toBlocks₁₂)ᴴ = 1 := by sorry
