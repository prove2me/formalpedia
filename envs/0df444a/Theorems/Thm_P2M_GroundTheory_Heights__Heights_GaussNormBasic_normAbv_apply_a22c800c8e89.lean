-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_normAbv_apply_a22c800c8e89
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_normAbv_apply_a22c800c8e89
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:36.35706+00:00
-- url     : https://prove2.me/theorems/ec1b7fc5-8a3c-4b08-a3da-c74b25076a5a
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic norm Abv apply a22c800c8e89: P2 M Ground Theory Heights  Heights Gauss Norm Basic norm Abv apply a22c800c8e89
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic norm Abv apply a22c800c8e89 construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic norm Abv apply a22c800c8e89 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L16-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PGaussNormBasic
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
open GroundTheory.Heights₂.Heights.GaussNormBasic
variable {L : Type*} [NormedField L] [IsUltrametricDist L]
omit [IsUltrametricDist L]

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_normAbv_apply_a22c800c8e89 (x : L) : normAbv L x = ‖x‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«normAbv_apply» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_normAbv_apply_a22c800c8e89
