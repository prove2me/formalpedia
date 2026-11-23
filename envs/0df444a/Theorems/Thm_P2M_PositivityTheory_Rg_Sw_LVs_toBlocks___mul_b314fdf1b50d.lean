-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_b314fdf1b50d
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_b314fdf1b50d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:35.493791+00:00
-- url     : https://prove2.me/theorems/7232758d-4a20-451a-a2cc-3fa07b767a6d
-- title:
--   P2 M Positivity Theory Rg Sw LVs to Blocks   mul b314fdf1b50d: P2 M Positivity Theory Rg Sw LVs to Blocks   mul b314fdf1b50d
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs to Blocks   mul b314fdf1b50d construction uses the P2 M Positivity Theory Rg Sw LVs to Blocks   mul b314fdf1b50d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L31-L34

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulInverseCayley
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_b314fdf1b50d (A B : M2 n) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«toBlocks₂₂_mul» := P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_b314fdf1b50d
