-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inv_blocks_of_InG
-- name    : PositivityTheory.Rg.Sw.LVs.inv_blocks_of_InG
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:07.044802+00:00
-- url     : https://prove2.me/theorems/d60febab-b7b2-4333-b8c0-b91a1d704b20
-- title:
--   LVs: inv blocks of In G
-- statement:
--   The LVs construction uses the inv blocks of In G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L190-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/DpDual.lean#L190-L194

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

theorem PositivityTheory.Rg.Sw.LVs.inv_blocks_of_InG {x : M2 n} (hx : InG x) :
    x⁻¹ = Matrix.fromBlocks (x.toBlocks₂₂)ᴴ (-(x.toBlocks₁₂)ᴴ) (-(x.toBlocks₂₁)ᴴ) (x.toBlocks₁₁)ᴴ := by sorry
