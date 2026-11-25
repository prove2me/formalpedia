-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_le_ker_add408c5818c
-- name    : P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_le_ker_add408c5818c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:31.323613+00:00
-- url     : https://prove2.me/theorems/011f6073-29dc-55c4-982c-d10bd3a4ad60
-- title:
--   P2 M Ground Theory Heights  Heights rabinowitsch Ideal le ker add408c5818c: P2 M Ground Theory Heights  Heights rabinowitsch Ideal le ker add408c5818c
-- statement:
--   The P2 M Ground Theory Heights  Heights rabinowitsch Ideal le ker add408c5818c construction uses the P2 M Ground Theory Heights  Heights rabinowitsch Ideal le ker add408c5818c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RadicalAwayRabinowitsch.lean#L49-L58

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

theorem P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_le_ker_add408c5818c (K : Ideal (MvPolynomial ι R)) (g : MvPolynomial ι R) :
    rabinowitschIdeal K g ≤ RingHom.ker (rabinowitschEval K g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«rabinowitschIdeal_le_ker» := P2M_GroundTheory_Heights__Heights_rabinowitschIdeal_le_ker_add408c5818c
