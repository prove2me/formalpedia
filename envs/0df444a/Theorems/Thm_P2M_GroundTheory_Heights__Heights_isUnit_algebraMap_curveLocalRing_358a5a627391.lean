-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_curveLocalRing_358a5a627391
-- name    : P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_curveLocalRing_358a5a627391
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:59.221361+00:00
-- url     : https://prove2.me/theorems/b3ec23f6-ded6-4fa7-a5a9-055190768f2d
-- title:
--   P2 M Ground Theory Heights  Heights is Unit algebra Map curve Local Ring 358a5a627391: P2 M Ground Theory Heights  Heights is Unit algebra Map curve Local Ring 358a5a627391
-- statement:
--   The P2 M Ground Theory Heights  Heights is Unit algebra Map curve Local Ring 358a5a627391 construction uses the P2 M Ground Theory Heights  Heights is Unit algebra Map curve Local Ring 358a5a627391 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveNormalisationLength.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveNormalisationLength.lean#L44-L49

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

theorem P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_curveLocalRing_358a5a627391 (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) (hf : eval q f ≠ 0) :
    IsUnit (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isUnit_algebraMap_curveLocalRing» := P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_curveLocalRing_358a5a627391
