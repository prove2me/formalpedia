-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_rename_mem_rabinowitschIdeal_iff_3875ac6396bd
-- name    : P2M_GroundTheory_Heights__Heights_rename_mem_rabinowitschIdeal_iff_3875ac6396bd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:59.490257+00:00
-- url     : https://prove2.me/theorems/ae5350f3-c5ea-4e4d-8bcf-f43f9df9d7c2
-- title:
--   P2 M Ground Theory Heights  Heights rename mem rabinowitsch Ideal iff 3875ac6396bd: P2 M Ground Theory Heights  Heights rename mem rabinowitsch Ideal iff 3875ac6396bd
-- statement:
--   The P2 M Ground Theory Heights  Heights rename mem rabinowitsch Ideal iff 3875ac6396bd construction uses the P2 M Ground Theory Heights  Heights rename mem rabinowitsch Ideal iff 3875ac6396bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L60-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L60-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RadicalAwayRabinowitsch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*}

theorem P2M_GroundTheory_Heights__Heights_rename_mem_rabinowitschIdeal_iff_3875ac6396bd (K : Ideal (MvPolynomial ι R)) (g f : MvPolynomial ι R) :
    rename some f ∈ rabinowitschIdeal K g ↔ ∃ k : ℕ, g ^ k * f ∈ K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«rename_mem_rabinowitschIdeal_iff» := P2M_GroundTheory_Heights__Heights_rename_mem_rabinowitschIdeal_iff_3875ac6396bd
