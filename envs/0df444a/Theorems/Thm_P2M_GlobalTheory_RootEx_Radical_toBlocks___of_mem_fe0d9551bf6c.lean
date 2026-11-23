-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___of_mem_fe0d9551bf6c
-- name    : P2M_GlobalTheory_RootEx_Radical_toBlocks___of_mem_fe0d9551bf6c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:37.401016+00:00
-- url     : https://prove2.me/theorems/cede9d44-085d-4dde-8d9e-55c2c3742cf5
-- title:
--   P2 M Global Theory Root Ex Radical to Blocks   of mem fe0d9551bf6c: P2 M Global Theory Root Ex Radical to Blocks   of mem fe0d9551bf6c
-- statement:
--   The P2 M Global Theory Root Ex Radical to Blocks   of mem fe0d9551bf6c construction uses the P2 M Global Theory Root Ex Radical to Blocks   of mem fe0d9551bf6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L99-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L99-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem P2M_GlobalTheory_RootEx_Radical_toBlocks___of_mem_fe0d9551bf6c {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    g.val.toBlocks₁₁ = 1 := by sorry

alias «GlobalTheory».«RootEx».«Radical».«toBlocks₁₁_of_mem» := P2M_GlobalTheory_RootEx_Radical_toBlocks___of_mem_fe0d9551bf6c
