-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_comap_curveLocalRing_strictMono_4510b04ac414
-- name    : P2M_GroundTheory_Heights__Heights_comap_curveLocalRing_strictMono_4510b04ac414
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:56.643879+00:00
-- url     : https://prove2.me/theorems/50634998-d3cf-4429-b187-2b03909e2398
-- title:
--   P2 M Ground Theory Heights  Heights comap curve Local Ring strict Mono 4510b04ac414: P2 M Ground Theory Heights  Heights comap curve Local Ring strict Mono 4510b04ac414
-- statement:
--   The P2 M Ground Theory Heights  Heights comap curve Local Ring strict Mono 4510b04ac414 construction uses the P2 M Ground Theory Heights  Heights comap curve Local Ring strict Mono 4510b04ac414 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalDimComponentBound.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalDimComponentBound.lean#L13-L20

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

theorem P2M_GroundTheory_Heights__Heights_comap_curveLocalRing_strictMono_4510b04ac414 (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    StrictMono (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«comap_curveLocalRing_strictMono» := P2M_GroundTheory_Heights__Heights_comap_curveLocalRing_strictMono_4510b04ac414
