-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_isNonarchimedean_normAbv_86b0b9ad6e8c
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_isNonarchimedean_normAbv_86b0b9ad6e8c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:30:50.723407+00:00
-- url     : https://prove2.me/theorems/05828142-7c36-49f5-8aac-b5253353c90c
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic is Nonarchimedean norm Abv 86b0b9ad6e8c: P2 M Ground Theory Heights  Heights Gauss Norm Basic is Nonarchimedean norm Abv 86b0b9ad6e8c
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic is Nonarchimedean norm Abv 86b0b9ad6e8c construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic is Nonarchimedean norm Abv 86b0b9ad6e8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L18-L19

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

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_isNonarchimedean_normAbv_86b0b9ad6e8c : IsNonarchimedean (normAbv L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«isNonarchimedean_normAbv» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_isNonarchimedean_normAbv_86b0b9ad6e8c
