-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_mem_of_unique_extension_3c111369f05d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_mem_of_unique_extension_3c111369f05d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:30.045819+00:00
-- url     : https://prove2.me/theorems/b5d2c950-aafa-5059-bfee-bb4a7b2acfa5
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend mem of unique extension 3c111369f05d: P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend mem of unique extension
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend mem of unique extension 3c111369f05d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend mem of unique extension 3c111369f05d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L217-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L217-L249

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend
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
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_mem_of_unique_extension_3c111369f05d {Ω : Type*} [Field Ω] [CharZero Ω] (A : Subalgebra ℚ Ω) [Algebra.FiniteType ℚ A]
    (θ : Ω) (hθ : IsIntegral ℚ θ)
    (huniq : ∀ w w' : Algebra.adjoin A {θ} →+* ℂ,
      w.comp (algebraMap A (Algebra.adjoin A {θ})) = w'.comp (algebraMap A (Algebra.adjoin A {θ})) →
        w ⟨θ, Algebra.subset_adjoin rfl⟩ = w' ⟨θ, Algebra.subset_adjoin rfl⟩) :
    θ ∈ A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ConstantsDescend».«mem_of_unique_extension» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_mem_of_unique_extension_3c111369f05d
