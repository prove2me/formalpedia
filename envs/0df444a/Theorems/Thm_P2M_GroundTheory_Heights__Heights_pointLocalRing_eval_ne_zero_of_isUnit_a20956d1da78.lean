-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_pointLocalRing_eval_ne_zero_of_isUnit_a20956d1da78
-- name    : P2M_GroundTheory_Heights__Heights_pointLocalRing_eval_ne_zero_of_isUnit_a20956d1da78
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:21.985371+00:00
-- url     : https://prove2.me/theorems/9d86dbb0-f06d-4836-8fa4-1260b13134e4
-- title:
--   P2 M Ground Theory Heights  Heights point Local Ring eval ne zero of is Unit a20956d1da78: P2 M Ground Theory Heights  Heights point Local Ring eval ne zero of is Unit a20956d1da78
-- statement:
--   The P2 M Ground Theory Heights  Heights point Local Ring eval ne zero of is Unit a20956d1da78 construction uses the P2 M Ground Theory Heights  Heights point Local Ring eval ne zero of is Unit a20956d1da78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L40-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PointLocalRingOrder.lean#L40-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder
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
open MvPolynomial Topology
noncomputable section
variable {σ : Type*}

theorem P2M_GroundTheory_Heights__Heights_pointLocalRing_eval_ne_zero_of_isUnit_a20956d1da78 (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) (u : MvPolynomial σ ℂ)
    (hu : IsUnit (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) u)) : eval w u ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«pointLocalRing_eval_ne_zero_of_isUnit» := P2M_GroundTheory_Heights__Heights_pointLocalRing_eval_ne_zero_of_isUnit_a20956d1da78
