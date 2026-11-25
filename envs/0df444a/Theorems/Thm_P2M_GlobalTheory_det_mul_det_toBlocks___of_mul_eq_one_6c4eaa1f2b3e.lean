-- Prove2me | Theorems.Thm_P2M_GlobalTheory_det_mul_det_toBlocks___of_mul_eq_one_6c4eaa1f2b3e
-- name    : P2M_GlobalTheory_det_mul_det_toBlocks___of_mul_eq_one_6c4eaa1f2b3e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:11.655425+00:00
-- url     : https://prove2.me/theorems/1acf2e84-bb1a-4046-b11e-5709b13b3324
-- title:
--   P2 M Global Theory det mul det to Blocks   of mul eq one 6c4eaa1f2b3e: P2 M Global Theory det mul det to Blocks   of mul eq one 6c4eaa1f2b3e
-- statement:
--   The P2 M Global Theory det mul det to Blocks   of mul eq one 6c4eaa1f2b3e construction uses the P2 M Global Theory det mul det to Blocks   of mul eq one 6c4eaa1f2b3e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PluckerMinorsProportional.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PluckerMinorsProportional.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PluckerMinorsProportional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem P2M_GlobalTheory_det_mul_det_toBlocks___of_mul_eq_one_6c4eaa1f2b3e {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X Y : Matrix (m ⊕ n) (m ⊕ n) K) (h : X * Y = 1) :
    X.det * Y.toBlocks₂₂.det = X.toBlocks₁₁.det := by sorry

alias «GlobalTheory».«det_mul_det_toBlocks₂₂_of_mul_eq_one» := P2M_GlobalTheory_det_mul_det_toBlocks___of_mul_eq_one_6c4eaa1f2b3e
