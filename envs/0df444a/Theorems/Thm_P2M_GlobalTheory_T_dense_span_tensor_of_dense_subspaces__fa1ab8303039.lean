-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_dense_span_tensor_of_dense_subspaces__fa1ab8303039
-- name    : P2M_GlobalTheory_T_dense_span_tensor_of_dense_subspaces__fa1ab8303039
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:17.48488+00:00
-- url     : https://prove2.me/theorems/182b2f79-6da7-442d-a757-61347241e38d
-- title:
--   P2 M Global Theory T dense span tensor of dense subspaces  fa1ab8303039: P2 M Global Theory T dense span tensor of dense subspaces  fa1ab8303039
-- statement:
--   The P2 M Global Theory T dense span tensor of dense subspaces  fa1ab8303039 construction uses the P2 M Global Theory T dense span tensor of dense subspaces  fa1ab8303039 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DenseSpanTensorOfDenseSubspacesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DenseSpanTensorOfDenseSubspacesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DenseSpanTensorOfDenseSubspaces
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DenseSpanTensorOfDenseSubspacesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_dense_span_tensor_of_dense_subspaces__fa1ab8303039 : ∀ {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (u : (∀ i, H i) → Hs) (W : ∀ i, Submodule ℂ (H i)), (∀ x y, ⟪u x, u y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → (∀ i, Dense (W i : Set (H i))) → Dense (Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i)))) : Set Hs) := by sorry

alias «GlobalTheory».«T».«dense_span_tensor_of_dense_subspaces'» := P2M_GlobalTheory_T_dense_span_tensor_of_dense_subspaces__fa1ab8303039
