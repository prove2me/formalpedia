-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_curveLocalRing_subsingleton_6e4911beb75a
-- name    : P2M_GroundTheory_Heights__Heights_curveLocalRing_subsingleton_6e4911beb75a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:16.270341+00:00
-- url     : https://prove2.me/theorems/1a080f15-3cfd-4631-9a70-2bb157a5ef08
-- title:
--   P2 M Ground Theory Heights  Heights curve Local Ring subsingleton 6e4911beb75a: P2 M Ground Theory Heights  Heights curve Local Ring subsingleton 6e4911beb75a
-- statement:
--   The P2 M Ground Theory Heights  Heights curve Local Ring subsingleton 6e4911beb75a construction uses the P2 M Ground Theory Heights  Heights curve Local Ring subsingleton 6e4911beb75a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveNormalisationLength.lean#L51-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveNormalisationLength.lean#L51-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
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

theorem P2M_GroundTheory_Heights__Heights_curveLocalRing_subsingleton_6e4911beb75a (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (hq : q ∉ zeroSet I) : Subsingleton (curveLocalRing I q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«curveLocalRing_subsingleton» := P2M_GroundTheory_Heights__Heights_curveLocalRing_subsingleton_6e4911beb75a
