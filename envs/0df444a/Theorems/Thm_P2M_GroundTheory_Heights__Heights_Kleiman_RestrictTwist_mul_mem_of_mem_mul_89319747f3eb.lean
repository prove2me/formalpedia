-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_mul_mem_of_mem_mul_89319747f3eb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_mul_mem_of_mem_mul_89319747f3eb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:09:50.787996+00:00
-- url     : https://prove2.me/theorems/dfb3ba78-1e38-4949-9a9e-7fc7302601d2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restrict Twist mul mem of mem mul 89319747f3eb: P2 M Ground Theory Heights  Heights Kleiman Restrict Twist mul mem of mem mul 89319747f3eb
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restrict Twist mul mem of mem mul 89319747f3eb construction uses the P2 M Ground Theory Heights  Heights Kleiman Restrict Twist mul mem of mem mul 89319747f3eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L229-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean#L229-L235

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_mul_mem_of_mem_mul_89319747f3eb {Q₁ Q₂ : SubSystem S x Ω} {I : Chart x} {v z : Ω}
    (hv : ∀ a ∈ Q₁.sub I, v * a ∈ chartRing S x I) (hz : z ∈ Q₂.sub I * Q₁.sub I) :
    v * z ∈ Q₂.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrictTwist».«mul_mem_of_mem_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrictTwist_mul_mem_of_mem_mul_89319747f3eb
