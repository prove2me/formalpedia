-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fieldCoord_conjMap_929ad50d655f
-- name    : P2M_GroundTheory_Heights__Heights_fieldCoord_conjMap_929ad50d655f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:41:30.088889+00:00
-- url     : https://prove2.me/theorems/862cb634-0545-430b-8c07-c1c475200aaa
-- title:
--   P2 M Ground Theory Heights  Heights field Coord conj Map 929ad50d655f: P2 M Ground Theory Heights  Heights field Coord conj Map 929ad50d655f
-- statement:
--   The P2 M Ground Theory Heights  Heights field Coord conj Map 929ad50d655f construction uses the P2 M Ground Theory Heights  Heights field Coord conj Map 929ad50d655f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L63-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_fieldCoord_conjMap_929ad50d655f (σ : K →+* ℂ) (t : Fibre σ K) :
    fieldCoord (conjugate σ) (conjMap σ K t) = starRingEnd ℂ (fieldCoord σ t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fieldCoord_conjMap» := P2M_GroundTheory_Heights__Heights_fieldCoord_conjMap_929ad50d655f
