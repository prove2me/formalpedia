-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_basis_adapted_to_cartan_involution__436ae184c2f0
-- name    : P2M_GlobalTheory_T_exists_basis_adapted_to_cartan_involution__436ae184c2f0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:21.184558+00:00
-- url     : https://prove2.me/theorems/09080dc0-16e7-43cd-83f9-2b93752129e1
-- title:
--   P2 M Global Theory T exists basis adapted to cartan involution  436ae184c2f0: P2 M Global Theory T exists basis adapted to cartan involution  436ae184c2f0
-- statement:
--   The P2 M Global Theory T exists basis adapted to cartan involution  436ae184c2f0 construction uses the P2 M Global Theory T exists basis adapted to cartan involution  436ae184c2f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasisAdaptedToCartanInvolutionStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasisAdaptedToCartanInvolutionStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisAdaptedToCartanInvolution
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisAdaptedToCartanInvolutionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_basis_adapted_to_cartan_involution__436ae184c2f0 : ∀ (n : ℕ) (G s : Matrix (Fin n) (Fin n) ℂ), s * s = 1 → sᴴ * G * s = G → (G * s).PosDef → ∃ (p q : ℕ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ) (B' : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ), B * B' = 1 ∧ B' * B = 1 ∧ Bᴴ * G * B = Matrix.fromBlocks 1 0 0 (-1) ∧ s * B = B * Matrix.fromBlocks 1 0 0 (-1) := by sorry

alias «GlobalTheory».«T».«exists_basis_adapted_to_cartan_involution'» := P2M_GlobalTheory_T_exists_basis_adapted_to_cartan_involution__436ae184c2f0
