-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_of_isSimpleModule_83467b0fb3cd
-- name    : P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_of_isSimpleModule_83467b0fb3cd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:23:41.909135+00:00
-- url     : https://prove2.me/theorems/26002954-49a3-4e36-b4d2-5f01d5219589
-- title:
--   P2 M Ground Theory Heights  Heights Inter card eq card residue Field of is Simple Module 83467b0fb3cd: P2 M Ground Theory Heights  Heights Inter card eq card residue Field of is Simple Module 83467b0f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter card eq card residue Field of is Simple Module 83467b0fb3cd construction uses the P2 M Ground Theory Heights  Heights Inter card eq card residue Field of is Simple Module 83467b0fb3cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLength.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLength.lean#L12-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open IsLocalRing
universe u v
variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_of_isSimpleModule_83467b0fb3cd (N : Type v) [AddCommGroup N] [Module R N]
    [IsSimpleModule R N] : Nat.card N = Nat.card (ResidueField R) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«card_eq_card_residueField_of_isSimpleModule» := P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_of_isSimpleModule_83467b0fb3cd
