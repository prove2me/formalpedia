-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_pow_length_9f7daccf84b2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_pow_length_9f7daccf84b2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:38.444713+00:00
-- url     : https://prove2.me/theorems/ace4c7a3-e1d7-4ada-a867-a361f6596173
-- title:
--   P2 M Ground Theory Heights  Heights Inter card eq card residue Field pow length 9f7daccf84b2: P2 M Ground Theory Heights  Heights Inter card eq card residue Field pow length 9f7daccf84b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter card eq card residue Field pow length 9f7daccf84b2 construction uses the P2 M Ground Theory Heights  Heights Inter card eq card residue Field pow length 9f7daccf84b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLength.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/CardLength.lean#L49-L54

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

theorem P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_pow_length_9f7daccf84b2 (M : Type v) [AddCommGroup M] [Module R M]
    (h : Module.length R M ≠ ⊤) :
    Nat.card M = Nat.card (ResidueField R) ^ (Module.length R M).toNat := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«card_eq_card_residueField_pow_length» := P2M_GroundTheory_Heights__Heights_Inter_card_eq_card_residueField_pow_length_9f7daccf84b2
