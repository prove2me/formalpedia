-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RootEx_Radical_toBlocks___embX_mul_110955ec0001
-- name    : P2M_GlobalTheory_RootEx_Radical_toBlocks___embX_mul_110955ec0001
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:27.639799+00:00
-- url     : https://prove2.me/theorems/c8c8cbd3-fa34-46b3-a1e3-90a85dfdd31e
-- title:
--   P2 M Global Theory Root Ex Radical to Blocks   emb X mul 110955ec0001: P2 M Global Theory Root Ex Radical to Blocks   emb X mul 110955ec0001
-- statement:
--   The P2 M Global Theory Root Ex Radical to Blocks   emb X mul 110955ec0001 construction uses the P2 M Global Theory Root Ex Radical to Blocks   emb X mul 110955ec0001 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L165-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnipotentRadicalBasic.lean#L165-L169

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

theorem P2M_GlobalTheory_RootEx_Radical_toBlocks___embX_mul_110955ec0001 (x : GL n k) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) :
    (embX c x * g).val.toBlocks₁₁ = x.val := by sorry

alias «GlobalTheory».«RootEx».«Radical».«toBlocks₁₁_embX_mul» := P2M_GlobalTheory_RootEx_Radical_toBlocks___embX_mul_110955ec0001
