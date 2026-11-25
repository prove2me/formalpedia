-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_map_994460cd29d0
-- name    : P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_map_994460cd29d0
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:48.14935+00:00
-- url     : https://prove2.me/theorems/44eead96-f11e-4166-8a9c-5984d485116c
-- title:
--   P2 M Ground Theory Heights  Heights rabinowitsch Ideal map 994460cd29d0: P2 M Ground Theory Heights  Heights rabinowitsch Ideal map 994460cd29d0
-- statement:
--   The P2 M Ground Theory Heights  Heights rabinowitsch Ideal map 994460cd29d0 construction uses the P2 M Ground Theory Heights  Heights rabinowitsch Ideal map 994460cd29d0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L17-L26

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

theorem P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_map_994460cd29d0 {R' : Type*} [CommRing R'] (φ : R →+* R')
    (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    (rabinowitschIdeal K g).map (MvPolynomial.map φ) =
      rabinowitschIdeal (K.map (MvPolynomial.map φ)) (MvPolynomial.map φ g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«rabinowitschIdeal_map» := P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_map_994460cd29d0
