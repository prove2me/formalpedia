-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_one_b05efafad2d2
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_one_b05efafad2d2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:26.320727+00:00
-- url     : https://prove2.me/theorems/7f25695d-9f7a-4ccc-8ba3-c92f34fd135c
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm one b05efafad2d2: P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm one b05efafad2d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm one b05efafad2d2 construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm one b05efafad2d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L47-L48

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

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_one_b05efafad2d2 {ι : Type*} : gaussNormOf (normAbv L) (1 : MvPolynomial ι L) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«gaussNorm_one» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_one_b05efafad2d2
