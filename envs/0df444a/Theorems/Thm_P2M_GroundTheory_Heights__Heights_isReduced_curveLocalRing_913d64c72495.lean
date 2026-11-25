-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_curveLocalRing_913d64c72495
-- name    : P2M_GroundTheory_Heights__Heights_isReduced_curveLocalRing_913d64c72495
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:08:12.609859+00:00
-- url     : https://prove2.me/theorems/6fe2f735-eb5a-47e6-9a0b-32bd5f85ecb3
-- title:
--   P2 M Ground Theory Heights  Heights is Reduced curve Local Ring 913d64c72495: P2 M Ground Theory Heights  Heights is Reduced curve Local Ring 913d64c72495
-- statement:
--   The P2 M Ground Theory Heights  Heights is Reduced curve Local Ring 913d64c72495 construction uses the P2 M Ground Theory Heights  Heights is Reduced curve Local Ring 913d64c72495 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CurveNormalisationFiniteLemmas.lean#L105-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/CurveNormalisationFiniteLemmas.lean#L105-L113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
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
open MvPolynomial ComplexSets FieldNumbers
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_isReduced_curveLocalRing_913d64c72495 {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (h : IsRadicalAt I q) : IsReduced (curveLocalRing I q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isReduced_curveLocalRing» := P2M_GroundTheory_Heights__Heights_isReduced_curveLocalRing_913d64c72495
