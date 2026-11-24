-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_algebraMap_curveNormalisation_injective_fe83821bff87
-- name    : P2M_GroundTheory_Heights__Heights_algebraMap_curveNormalisation_injective_fe83821bff87
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:44.366531+00:00
-- url     : https://prove2.me/theorems/a116e61b-d3b3-4448-a2f5-e7e867d16053
-- title:
--   P2 M Ground Theory Heights  Heights algebra Map curve Normalisation injective fe83821bff87: P2 M Ground Theory Heights  Heights algebra Map curve Normalisation injective fe83821bff87
-- statement:
--   The P2 M Ground Theory Heights  Heights algebra Map curve Normalisation injective fe83821bff87 construction uses the P2 M Ground Theory Heights  Heights algebra Map curve Normalisation injective fe83821bff87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveNormalisationLength.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveNormalisationLength.lean#L60-L63

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

theorem P2M_GroundTheory_Heights__Heights_algebraMap_curveNormalisation_injective_fe83821bff87 (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    Function.Injective (algebraMap (curveLocalRing I q) (curveNormalisation I q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«algebraMap_curveNormalisation_injective» := P2M_GroundTheory_Heights__Heights_algebraMap_curveNormalisation_injective_fe83821bff87
