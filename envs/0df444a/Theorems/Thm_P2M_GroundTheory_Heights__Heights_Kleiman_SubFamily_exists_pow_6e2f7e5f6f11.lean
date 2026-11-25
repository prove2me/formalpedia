-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubFamily_exists_pow_6e2f7e5f6f11
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubFamily_exists_pow_6e2f7e5f6f11
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:59:05.993902+00:00
-- url     : https://prove2.me/theorems/81b999d2-f3bd-41e8-a15a-7e77de1871dd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub Family exists pow 6e2f7e5f6f11: P2 M Ground Theory Heights  Heights Kleiman Sub Family exists pow 6e2f7e5f6f11
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub Family exists pow 6e2f7e5f6f11 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub Family exists pow 6e2f7e5f6f11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSubFamilyTwistPow.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSubFamilyTwistPow.lean#L68-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistPowSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubFamilyTwistPow
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
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubFamily_exists_pow_6e2f7e5f6f11 (Q : SubFamily S x Ω) (n : ℕ) :
    ∃ P : SubFamily S x Ω, P.toSubSystem = Q.toSubSystem.pow n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubFamily».«exists_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_SubFamily_exists_pow_6e2f7e5f6f11
