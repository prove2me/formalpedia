-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_exists_common_b30485fec4df
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_exists_common_b30485fec4df
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:46.205046+00:00
-- url     : https://prove2.me/theorems/2816d294-e361-45a2-9785-763ab35c8f86
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded exists common b30485fec4df: P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded exists common b30485fec4df
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded exists common b30485fec4df construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Serre Graded exists common b30485fec4df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean#L152-L156

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded
open Polynomial
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_exists_common_b30485fec4df {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (h : ∀ i ∈ s, ∃ D, ∀ D', D ≤ D' → P i D') : ∃ D, ∀ i ∈ s, P i D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«SerreGraded».«exists_common» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_SerreGraded_exists_common_b30485fec4df
