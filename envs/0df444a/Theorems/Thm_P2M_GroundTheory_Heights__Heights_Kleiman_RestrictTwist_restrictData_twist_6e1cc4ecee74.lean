-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twist_6e1cc4ecee74
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twist_6e1cc4ecee74
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:09:55.407384+00:00
-- url     : https://prove2.me/theorems/85ce853e-dcf1-519c-8a5c-b8fe4043d6d3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist restrict Data twist 6e1cc4ecee74: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist restrict Data twist 6e1cc4ecee74
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist restrict Data twist 6e1cc4ecee74 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist restrict Data twist 6e1cc4ecee74 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L297-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L297-L357

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
variable {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twist_6e1cc4ecee74 {Q₁ Q₂ : LineBundle S x} {Q₁' Q₂' : LineBundle S y} {r₁ r₂ : Ω → K'}
    (h₁ : RestrictData Q₁.toSubSystem hxy Q₁'.toSubSystem r₁)
    (h₂ : RestrictData Q₂.toSubSystem hxy Q₂'.toSubSystem r₂) :
    ∃ r : Ω → K', RestrictData (Q₁.toSubSystem.twist Q₂.toSubSystem) hxy
      (Q₁'.toSubSystem.twist Q₂'.toSubSystem) r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«restrictData_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_restrictData_twist_6e1cc4ecee74
