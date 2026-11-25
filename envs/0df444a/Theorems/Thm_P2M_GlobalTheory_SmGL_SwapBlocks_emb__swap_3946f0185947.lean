-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SmGL_SwapBlocks_emb__swap_3946f0185947
-- name    : P2M_GlobalTheory_SmGL_SwapBlocks_emb__swap_3946f0185947
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:11:36.092061+00:00
-- url     : https://prove2.me/theorems/e972d9e1-e304-5f88-add9-91d0cfbc5174
-- title:
--   P2 M Global Theory Sm GL Swap Blocks emb  swap 3946f0185947: P2 M Global Theory Sm GL Swap Blocks emb  swap 3946f0185947
-- statement:
--   The P2 M Global Theory Sm GL Swap Blocks emb  swap 3946f0185947 construction uses the P2 M Global Theory Sm GL Swap Blocks emb  swap 3946f0185947 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LowerEquivUpperSwap.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LowerEquivUpperSwap.lean#L29-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.SwapBlocks
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n]

theorem P2M_GlobalTheory_SmGL_SwapBlocks_emb__swap_3946f0185947 (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    emb₂ R e g = emb₂ R ((Equiv.sumComm b a).trans e) (g.2, g.1) := by sorry

alias «GlobalTheory».«SmGL».«SwapBlocks».«emb₂_swap» := P2M_GlobalTheory_SmGL_SwapBlocks_emb__swap_3946f0185947
