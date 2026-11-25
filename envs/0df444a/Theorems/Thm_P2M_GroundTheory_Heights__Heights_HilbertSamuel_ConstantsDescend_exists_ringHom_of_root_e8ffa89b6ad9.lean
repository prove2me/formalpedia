-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_ringHom_of_root_e8ffa89b6ad9
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_ringHom_of_root_e8ffa89b6ad9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:50.189732+00:00
-- url     : https://prove2.me/theorems/752ce862-b930-4cd5-a03d-ff36c6d3ab31
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists ring Hom of root e8ffa89b6ad9: P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists ring Hom of root
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists ring Hom of root e8ffa89b6ad9 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Constants Descend exists ring Hom of root e8ffa89b6ad9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L21-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConstantsDescend.lean#L21-L62

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_ringHom_of_root_e8ffa89b6ad9 (θ : B) (hgen : Algebra.adjoin A {θ} = ⊤) (I : Ideal A) [I.IsMaximal]
    (σ : A ⧸ I →+* ℂ) (β : ℂ)
    (hβ : ((minpoly (A ⧸ I) (Ideal.Quotient.mk (I.map (algebraMap A B)) θ)).map σ).IsRoot β) :
    ∃ w : B →+* ℂ, w.comp (algebraMap A B) = σ.comp (Ideal.Quotient.mk I) ∧ w θ = β := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ConstantsDescend».«exists_ringHom_of_root» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_exists_ringHom_of_root_e8ffa89b6ad9
