-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_primitive_9418c28bff33
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_primitive_9418c28bff33
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:45.000828+00:00
-- url     : https://prove2.me/theorems/567503ac-5573-466e-933d-eba5cc82e4a1
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists primitive 9418c28bff33: P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists primitive 9418c28bff33
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists primitive 9418c28bff33 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists primitive 9418c28bff33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L197-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L197-L215

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_primitive_9418c28bff33 {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (S : Finset Ω)
    (hS : ∀ s ∈ S, IsIntegral F s) :
    ∃ θ : Ω, IsIntegral F θ ∧ θ ∈ Algebra.adjoin F (S : Set Ω) ∧
      ∀ x ∈ IntermediateField.adjoin F (S : Set Ω), x ∈ Algebra.adjoin F {θ} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ConstantsDescend».«exists_primitive» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_primitive_9418c28bff33
