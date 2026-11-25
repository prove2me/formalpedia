-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_finrank_add_finrank_le_finrank_inf_comap_sub_id__6c5166c7b064
-- name    : P2M_GlobalTheory_T_finrank_add_finrank_le_finrank_inf_comap_sub_id__6c5166c7b064
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:26.393799+00:00
-- url     : https://prove2.me/theorems/cfbcf656-18ec-4cbe-9e83-24bbce64077e
-- title:
--   P2 M Global Theory T finrank add finrank le finrank inf comap sub id  6c5166c7b064: P2 M Global Theory T finrank add finrank le finrank inf comap sub id  6c5166c7b064
-- statement:
--   The P2 M Global Theory T finrank add finrank le finrank inf comap sub id  6c5166c7b064 construction uses the P2 M Global Theory T finrank add finrank le finrank inf comap sub id  6c5166c7b064 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAddFinrankLeFinrankInfComapSubIdStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankAddFinrankLeFinrankInfComapSubIdStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAddFinrankLeFinrankInfComapSubId
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankAddFinrankLeFinrankInfComapSubIdStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_finrank_add_finrank_le_finrank_inf_comap_sub_id__6c5166c7b064 : ∀ (k : Type) [Field k] (M W : Type) [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W] (D R : Submodule k M) [FiniteDimensional k ↥D] (F : M →ₗ[k] M) (B : M →ₗ[k] W →ₗ[k] k), R ≤ D → (∀ x ∈ D, F x ∈ D) → (∀ x ∈ R, ∀ w, B x w = 0) → (∀ x ∈ D, ∀ w, B (F x) w = B x w) → (∀ w, (∀ x ∈ D, B x w = 0) → w = 0) → finrank k W + finrank k ↥R ≤ finrank k ↥(D ⊓ R.comap (F - LinearMap.id)) := by sorry

alias «GlobalTheory».«T».«finrank_add_finrank_le_finrank_inf_comap_sub_id'» := P2M_GlobalTheory_T_finrank_add_finrank_le_finrank_inf_comap_sub_id__6c5166c7b064
