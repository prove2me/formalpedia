-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_re_inner_le_on_image_of_intertwining__54cc34e9f289
-- name    : P2M_GlobalTheory_T_re_inner_le_on_image_of_intertwining__54cc34e9f289
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:40:01.668877+00:00
-- url     : https://prove2.me/theorems/8b509b64-871c-595d-b8e3-cbc9a3d7144e
-- title:
--   P2 M Global Theory T re inner le on image of intertwining  54cc34e9f289: P2 M Global Theory T re inner le on image of intertwining  54cc34e9f289
-- statement:
--   The P2 M Global Theory T re inner le on image of intertwining  54cc34e9f289 construction uses the P2 M Global Theory T re inner le on image of intertwining  54cc34e9f289 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ReInnerLeOnImageOfIntertwiningStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ReInnerLeOnImageOfIntertwiningStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwining
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ReInnerLeOnImageOfIntertwiningStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_re_inner_le_on_image_of_intertwining__54cc34e9f289 : ∀ (T N : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T] [NormedAddCommGroup N] [InnerProductSpace ℂ N] (Φ : T →ₗ[ℂ] N) (A : T →ₗ[ℂ] T) (B : N →ₗ[ℂ] N) (C : ℝ), A.IsSymmetric → B.IsSymmetric → (∀ x, Φ (A x) = B (Φ x)) → (∀ x, (⟪x, A x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) → ∀ x, (⟪Φ x, B (Φ x)⟫_ℂ).re ≤ C * ‖Φ x‖ ^ 2 := by sorry

alias «GlobalTheory».«T».«re_inner_le_on_image_of_intertwining'» := P2M_GlobalTheory_T_re_inner_le_on_image_of_intertwining__54cc34e9f289
