-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_pointLocalRing_0914499906a4
-- name    : P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_pointLocalRing_0914499906a4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:59.007497+00:00
-- url     : https://prove2.me/theorems/51d8531f-2508-4aaf-96bd-c62340f30c04
-- title:
--   P2 M Ground Theory Heights  Heights is Unit algebra Map point Local Ring 0914499906a4: P2 M Ground Theory Heights  Heights is Unit algebra Map point Local Ring 0914499906a4
-- statement:
--   The P2 M Ground Theory Heights  Heights is Unit algebra Map point Local Ring 0914499906a4 construction uses the P2 M Ground Theory Heights  Heights is Unit algebra Map point Local Ring 0914499906a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelPlace.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalModelPlace.lean#L29-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
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
variable {σ : Type*}

theorem P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_pointLocalRing_0914499906a4 (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (f : MvPolynomial σ ℂ)
    (hf : eval w f ≠ 0) : IsUnit (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isUnit_algebraMap_pointLocalRing» := P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_pointLocalRing_0914499906a4
