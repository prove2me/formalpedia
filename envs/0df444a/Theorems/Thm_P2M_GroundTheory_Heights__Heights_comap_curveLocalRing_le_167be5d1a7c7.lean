-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_comap_curveLocalRing_le_167be5d1a7c7
-- name    : P2M_GroundTheory_Heights__Heights_comap_curveLocalRing_le_167be5d1a7c7
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:59.407767+00:00
-- url     : https://prove2.me/theorems/68993085-1310-4cca-85f7-46a9e4e44c06
-- title:
--   P2 M Ground Theory Heights  Heights comap curve Local Ring le 167be5d1a7c7: P2 M Ground Theory Heights  Heights comap curve Local Ring le 167be5d1a7c7
-- statement:
--   The P2 M Ground Theory Heights  Heights comap curve Local Ring le 167be5d1a7c7 construction uses the P2 M Ground Theory Heights  Heights comap curve Local Ring le 167be5d1a7c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalDimComponentBound.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalDimComponentBound.lean#L34-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalDimComponentBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimComponentBound
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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_comap_curveLocalRing_le_167be5d1a7c7 (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal ≤
      RingHom.ker (eval q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«comap_curveLocalRing_le» := P2M_GroundTheory_Heights__Heights_comap_curveLocalRing_le_167be5d1a7c7
