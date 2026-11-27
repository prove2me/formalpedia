-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_intertwiner_fixes_of_local_vacuum__5ae4e3e48537
-- name    : P2M_GlobalTheory_T_intertwiner_fixes_of_local_vacuum__5ae4e3e48537
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:39.3956+00:00
-- url     : https://prove2.me/theorems/2c3bb5fd-5be2-4343-af75-89822885fb8e
-- title:
--   P2 M Global Theory T intertwiner fixes of local vacuum  5ae4e3e48537: P2 M Global Theory T intertwiner fixes of local vacuum  5ae4e3e48537
-- statement:
--   The P2 M Global Theory T intertwiner fixes of local vacuum  5ae4e3e48537 construction uses the P2 M Global Theory T intertwiner fixes of local vacuum  5ae4e3e48537 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntertwinerFixesOfLocalVacuumStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntertwinerFixesOfLocalVacuumStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntertwinerFixesOfLocalVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HeisenbergIntertwiningSumsCompEqIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormalizedHeisenbergIntertwinerComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsWeilRepresentationHeisenberg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanHeisenbergTranslatesVacuumEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntertwinerFixesOfLocalVacuumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_intertwiner_fixes_of_local_vacuum__5ae4e3e48537 : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X) (T : M →ₗ[ℂ] M), (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = e) → ∀ P : X →ₗ[R] X, (∀ x y, γ (P x) y = γ x (P y)) → (∀ a ∈ A, P a ∈ A) → (∀ x, φ (x - P x) = x - P x) → ∀ m : M, (∀ a ∈ A, W (P a) m = m) → T m = m := by sorry

alias «GlobalTheory».«T».«intertwiner_fixes_of_local_vacuum'» := P2M_GlobalTheory_T_intertwiner_fixes_of_local_vacuum__5ae4e3e48537
