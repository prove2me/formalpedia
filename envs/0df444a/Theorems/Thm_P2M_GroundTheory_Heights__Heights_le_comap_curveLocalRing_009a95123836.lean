-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_comap_curveLocalRing_009a95123836
-- name    : P2M_GroundTheory_Heights__Heights_le_comap_curveLocalRing_009a95123836
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:00.877648+00:00
-- url     : https://prove2.me/theorems/1e019e24-aae7-47d6-83e5-93f68c605244
-- title:
--   P2 M Ground Theory Heights  Heights le comap curve Local Ring 009a95123836: P2 M Ground Theory Heights  Heights le comap curve Local Ring 009a95123836
-- statement:
--   The P2 M Ground Theory Heights  Heights le comap curve Local Ring 009a95123836 construction uses the P2 M Ground Theory Heights  Heights le comap curve Local Ring 009a95123836 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalDimComponentBound.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalDimComponentBound.lean#L22-L32

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

theorem P2M_GroundTheory_Heights__Heights_le_comap_curveLocalRing_009a95123836 (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    I ≤ (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«le_comap_curveLocalRing» := P2M_GroundTheory_Heights__Heights_le_comap_curveLocalRing_009a95123836
