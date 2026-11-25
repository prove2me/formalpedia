-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_algebraMap_surjective_46fcacb94b77
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_algebraMap_surjective_46fcacb94b77
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:52.137829+00:00
-- url     : https://prove2.me/theorems/42b80bae-cb0e-4172-9ae3-39a474906ce6
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend algebra Map surjective 46fcacb94b77: P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend algebra Map surjective 46
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend algebra Map surjective 46fcacb94b77 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend algebra Map surjective 46fcacb94b77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L121-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L121-L166

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
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra ℚ A] [Algebra.FiniteType ℚ A]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_algebraMap_surjective_46fcacb94b77 (hinj : Function.Injective (algebraMap A B)) (θ : B)
    (hgen : Algebra.adjoin A {θ} = ⊤) (p : ℚ[X]) (hpm : p.Monic) (hps : p.Separable)
    (hp : aeval θ (p.map (algebraMap ℚ A)) = 0)
    (huniq : ∀ w w' : B →+* ℂ, w.comp (algebraMap A B) = w'.comp (algebraMap A B) → w θ = w' θ) :
    Function.Surjective (algebraMap A B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ConstantsDescend».«algebraMap_surjective» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_algebraMap_surjective_46fcacb94b77
