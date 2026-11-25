-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_eq_of_subset_43355d35aad8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_eq_of_subset_43355d35aad8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:07.855037+00:00
-- url     : https://prove2.me/theorems/fef98b41-a17b-40c2-ad97-f34b4b10368d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res eq of subset 43355d35aad8: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res eq of subset 43355d35aad8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res eq of subset 43355d35aad8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res eq of subset 43355d35aad8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L270-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L270-L295

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_eq_of_subset_43355d35aad8 {Q₁ Q₂ : SubSystem S x Ω} {Q₁' Q₂' : SubSystem S y K'} {r₁ r₂ : Ω → K'}
    (h₁ : RestrictData Q₁ hxy Q₁' r₁) (h₂ : RestrictData Q₂ hxy Q₂' r₂) {I K : Chart y}
    (hIK : I.1 ⊆ K.1) {l l' : List (Ω × Ω)}
    (hl : ∀ p ∈ l, p.1 ∈ Q₁.sub (liftChart hxy I) ∧
      ∀ a ∈ Q₁.sub (liftChart hxy I), p.2 * a ∈ chartRing S x (liftChart hxy I))
    (hl1 : (l.map fun p => p.1 * p.2).sum = 1)
    (hl' : ∀ p ∈ l', p.1 ∈ Q₁.sub (liftChart hxy K) ∧
      ∀ a ∈ Q₁.sub (liftChart hxy K), p.2 * a ∈ chartRing S x (liftChart hxy K))
    (hl1' : (l'.map fun p => p.1 * p.2).sum = 1) {z : Ω}
    (hz : z ∈ Q₂.sub (liftChart hxy I) * Q₁.sub (liftChart hxy I)) :
    prodRes r₁ r₂ l z = prodRes r₁ r₂ l' z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«prodRes_eq_of_subset» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_eq_of_subset_43355d35aad8
