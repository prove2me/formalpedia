-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_isotropic_dual_of_skew_matrix__234181029e55
-- name    : P2M_GlobalTheory_T_exists_isotropic_dual_of_skew_matrix__234181029e55
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:09.218949+00:00
-- url     : https://prove2.me/theorems/d0f9f6db-d5f8-5c10-82af-499b07780a99
-- title:
--   P2 M Global Theory T exists isotropic dual of skew matrix  234181029e55: P2 M Global Theory T exists isotropic dual of skew matrix  234181029e55
-- statement:
--   The P2 M Global Theory T exists isotropic dual of skew matrix  234181029e55 construction uses the P2 M Global Theory T exists isotropic dual of skew matrix  234181029e55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIsotropicDualOfSkewMatrixStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIsotropicDualOfSkewMatrixStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIsotropicDualOfSkewMatrix
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIsotropicDualOfSkewMatrixStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_isotropic_dual_of_skew_matrix__234181029e55 : ∀ (r g : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε ψ : Fin g → Fin r → ℚ), Mqᵀ = -Mq → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, ψ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) → ∃ φ : Fin g → Fin r → ℚ, (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) ∧ (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) ∧ ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by sorry

alias «GlobalTheory».«T».«exists_isotropic_dual_of_skew_matrix'» := P2M_GlobalTheory_T_exists_isotropic_dual_of_skew_matrix__234181029e55
