-- Prove2me | Theorems.Thm_P2M_GlobalTheory_Div_BlockChangeDet_det_block_change__df4d8659a7d2
-- name    : P2M_GlobalTheory_Div_BlockChangeDet_det_block_change__df4d8659a7d2
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:05:23.753505+00:00
-- url     : https://prove2.me/theorems/cb21241e-affc-4485-a88d-114fae244c9c
-- title:
--   P2 M Global Theory Div Block Change Det det block change  df4d8659a7d2: P2 M Global Theory Div Block Change Det det block change  df4d8659a7d2
-- statement:
--   The P2 M Global Theory Div Block Change Det det block change  df4d8659a7d2 construction uses the P2 M Global Theory Div Block Change Det det block change  df4d8659a7d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetBlockChangeOfBasisViaTwoFamiliesImplicit.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetBlockChangeOfBasisViaTwoFamiliesImplicit.lean#L127-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetBlockChangeOfBasisViaTwoFamiliesImplicit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.BlockChangeDet
open Matrix

theorem P2M_GlobalTheory_Div_BlockChangeDet_det_block_change__df4d8659a7d2 : ∀ {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N] {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N),
    (∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) → ∀ (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F),
    (∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) → (∀ k, mu k = ∑ l, A k l • nu l) →
    (∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) →
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by sorry

alias «GlobalTheory».«Div».«BlockChangeDet».«det_block_change'» := P2M_GlobalTheory_Div_BlockChangeDet_det_block_change__df4d8659a7d2
