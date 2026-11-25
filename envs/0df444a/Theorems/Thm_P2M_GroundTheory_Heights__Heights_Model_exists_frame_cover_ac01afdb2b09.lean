-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_frame_cover_ac01afdb2b09
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_frame_cover_ac01afdb2b09
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:01.572238+00:00
-- url     : https://prove2.me/theorems/25f29c70-5fa2-4331-9706-66c721d9ca88
-- title:
--   P2 M Ground Theory Heights  Heights Model exists frame cover ac01afdb2b09: P2 M Ground Theory Heights  Heights Model exists frame cover ac01afdb2b09
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists frame cover ac01afdb2b09 construction uses the P2 M Ground Theory Heights  Heights Model exists frame cover ac01afdb2b09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrame.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrame.lean#L18-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_Model_exists_frame_cover_ac01afdb2b09 (A : Subalgebra ℤ Ω) (r : ℕ) (M : AddSubgroup E)
    (hloc : ∀ Q : Ideal A, Q.IsMaximal →
      ∃ h : Ω, ∃ hh : h ∈ A, (⟨h, hh⟩ : A) ∉ Q ∧ IsFrameAt A r M h) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ A) ∧ (∀ l, c l ∈ A) ∧ ∑ l, c l * f l = 1 ∧
      ∀ l, IsFrameAt A r M (f l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_frame_cover» := P2M_GroundTheory_Heights__Heights_Model_exists_frame_cover_ac01afdb2b09
