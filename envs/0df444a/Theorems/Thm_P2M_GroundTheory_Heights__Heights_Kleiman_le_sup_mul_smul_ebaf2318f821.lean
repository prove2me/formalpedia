-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_le_sup_mul_smul_ebaf2318f821
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_le_sup_mul_smul_ebaf2318f821
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:09:20.796446+00:00
-- url     : https://prove2.me/theorems/7f486b1a-b191-45ac-86d9-11f775f91fba
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman le sup mul smul ebaf2318f821: P2 M Ground Theory Heights  Heights Kleiman le sup mul smul ebaf2318f821
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman le sup mul smul ebaf2318f821 construction uses the P2 M Ground Theory Heights  Heights Kleiman le sup mul smul ebaf2318f821 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L83-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThree.lean#L83-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnW
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThree
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
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_le_sup_mul_smul_ebaf2318f821 {G F : Submodule A M} {P Q : Ideal A} (hP : F ≤ G ⊔ P • F)
    (hQ : F ≤ G ⊔ Q • F) : F ≤ G ⊔ (P * Q) • F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«le_sup_mul_smul» := P2M_GroundTheory_Heights__Heights_Kleiman_le_sup_mul_smul_ebaf2318f821
