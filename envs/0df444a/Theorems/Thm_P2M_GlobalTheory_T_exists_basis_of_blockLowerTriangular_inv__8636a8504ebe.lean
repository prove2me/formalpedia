-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_basis_of_blockLowerTriangular_inv__8636a8504ebe
-- name    : P2M_GlobalTheory_T_exists_basis_of_blockLowerTriangular_inv__8636a8504ebe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:35.780274+00:00
-- url     : https://prove2.me/theorems/f2edda97-1836-47ea-abdc-d7914540ac63
-- title:
--   P2 M Global Theory T exists basis of block Lower Triangular inv  8636a8504ebe: P2 M Global Theory T exists basis of block Lower Triangular inv  8636a8504ebe
-- statement:
--   The P2 M Global Theory T exists basis of block Lower Triangular inv  8636a8504ebe construction uses the P2 M Global Theory T exists basis of block Lower Triangular inv  8636a8504ebe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasisOfBlockLowerTriangularInvStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasisOfBlockLowerTriangularInvStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisOfBlockLowerTriangularInv
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisOfBlockLowerTriangularInvStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_basis_of_blockLowerTriangular_inv__8636a8504ebe : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M) (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O), P * P' = 1 → P' * P = 1 → (∀ i j, P (Sum.inl i) (Sum.inr j) = 0) → ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by sorry

alias «GlobalTheory».«T».«exists_basis_of_blockLowerTriangular_inv'» := P2M_GlobalTheory_T_exists_basis_of_blockLowerTriangular_inv__8636a8504ebe
