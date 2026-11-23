-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_03bb7bc462ab
-- name    : P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_03bb7bc462ab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:53.180816+00:00
-- url     : https://prove2.me/theorems/8fcb2b67-eda4-4b26-b258-d48ecae6f3a2
-- title:
--   P2 M Positivity Theory Rg Sw LVs to Blocks   mul 03bb7bc462ab: P2 M Positivity Theory Rg Sw LVs to Blocks   mul 03bb7bc462ab
-- statement:
--   The P2 M Positivity Theory Rg Sw LVs to Blocks   mul 03bb7bc462ab construction uses the P2 M Positivity Theory Rg Sw LVs to Blocks   mul 03bb7bc462ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SecondCayleyBlockMulInverseCayley.lean#L26-L29

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

theorem P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_03bb7bc462ab (A B : M2 n) :
    (A * B).toBlocks₂₁ = A.toBlocks₂₁ * B.toBlocks₁₁ + A.toBlocks₂₂ * B.toBlocks₂₁ := by sorry

alias «PositivityTheory».«Rg».«Sw».«LVs».«toBlocks₂₁_mul» := P2M_PositivityTheory_Rg_Sw_LVs_toBlocks___mul_03bb7bc462ab
