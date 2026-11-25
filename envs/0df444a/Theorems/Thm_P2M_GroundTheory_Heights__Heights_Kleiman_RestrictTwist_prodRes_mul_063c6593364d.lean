-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_mul_063c6593364d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_mul_063c6593364d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:09:22.837373+00:00
-- url     : https://prove2.me/theorems/d7648a9e-32f4-496a-b63d-e2a2bbddef80
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res mul 063c6593364d: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res mul 063c6593364d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res mul 063c6593364d construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist prod Res mul 063c6593364d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L246-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L246-L268

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_mul_063c6593364d {Q₁ Q₂ : SubSystem S x Ω} {Q₁' Q₂' : SubSystem S y K'} {r₁ r₂ : Ω → K'}
    (h₁ : RestrictData Q₁ hxy Q₁' r₁) (h₂ : RestrictData Q₂ hxy Q₂' r₂) (I : Chart y)
    {l : List (Ω × Ω)} (hl : ∀ p ∈ l, p.1 ∈ Q₁.sub (liftChart hxy I) ∧
      ∀ a ∈ Q₁.sub (liftChart hxy I), p.2 * a ∈ chartRing S x (liftChart hxy I))
    (hl1 : (l.map fun p => p.1 * p.2).sum = 1) {a b : Ω} (ha : a ∈ Q₁.sub (liftChart hxy I))
    (hb : b ∈ Q₂.sub (liftChart hxy I)) :
    prodRes r₁ r₂ l (b * a) = r₁ a * r₂ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«prodRes_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_prodRes_mul_063c6593364d
