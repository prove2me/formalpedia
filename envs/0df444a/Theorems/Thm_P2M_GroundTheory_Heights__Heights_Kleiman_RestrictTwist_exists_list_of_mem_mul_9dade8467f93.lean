-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_list_of_mem_mul_9dade8467f93
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_list_of_mem_mul_9dade8467f93
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:02:19.006796+00:00
-- url     : https://prove2.me/theorems/0f97a2aa-59e8-4f71-9340-bb393deb4c32
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists list of mem mul 9dade8467f93: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists list of mem mul 9dade8467f93
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists list of mem mul 9dade8467f93 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist exists list of mem mul 9dade8467f93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L162-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L162-L170

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_list_of_mem_mul_9dade8467f93 {A : Type*} [CommRing A] [Algebra A Ω] {P Q : Submodule A Ω} {z : Ω}
    (hz : z ∈ P * Q) :
    ∃ l : List (Ω × Ω), (∀ p ∈ l, p.1 ∈ P ∧ p.2 ∈ Q) ∧ (l.map fun p => p.1 * p.2).sum = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«exists_list_of_mem_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_exists_list_of_mem_mul_9dade8467f93
