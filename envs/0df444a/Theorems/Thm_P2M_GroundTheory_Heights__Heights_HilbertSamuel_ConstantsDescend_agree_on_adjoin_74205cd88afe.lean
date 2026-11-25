-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_agree_on_adjoin_74205cd88afe
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_agree_on_adjoin_74205cd88afe
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:52.576421+00:00
-- url     : https://prove2.me/theorems/3a2d4ca4-66ac-47e8-bde3-19d596192c24
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend agree on adjoin 74205cd88afe: P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend agree on adjoin 74205cd88afe
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend agree on adjoin 74205cd88afe construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend agree on adjoin 74205cd88afe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L251-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L251-L282

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_agree_on_adjoin_74205cd88afe {Ω : Type*} [Field Ω] [CharZero Ω] (R T : Subalgebra ℤ Ω) (A : Subalgebra ℚ Ω)
    (B : Subalgebra A Ω) (hRA : ∀ r ∈ R, r ∈ A) (θ : Ω) (hθB : θ ∈ B)
    (hTθ : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ {θ})
    (H : ∀ w w' : ↥(R ⊔ T) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom)
    (w w' : B →+* ℂ) (hw : w.comp (algebraMap A B) = w'.comp (algebraMap A B)) :
    ∀ x ∈ Algebra.adjoin ℚ (T : Set Ω), x ∈ (RingHom.eqLocus w w').map B.val.toRingHom := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ConstantsDescend».«agree_on_adjoin» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_agree_on_adjoin_74205cd88afe
