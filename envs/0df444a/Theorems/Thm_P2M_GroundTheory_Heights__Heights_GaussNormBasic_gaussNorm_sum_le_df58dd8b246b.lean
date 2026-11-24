-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_sum_le_df58dd8b246b
-- name    : P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_sum_le_df58dd8b246b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:48.401642+00:00
-- url     : https://prove2.me/theorems/987cc3ba-8fde-42f6-84c9-14da55c974fd
-- title:
--   P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm sum le df58dd8b246b: P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm sum le df58dd8b246b
-- statement:
--   The P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm sum le df58dd8b246b construction uses the P2 M Ground Theory Heights  Heights Gauss Norm Basic gauss Norm sum le df58dd8b246b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PGaussNormBasic.lean#L29-L34

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

theorem P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_sum_le_df58dd8b246b {ι β : Type*} (s : Finset β) (f : β → MvPolynomial ι L) {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ b ∈ s, gaussNormOf (normAbv L) (f b) ≤ r) :
    gaussNormOf (normAbv L) (∑ b ∈ s, f b) ≤ r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GaussNormBasic».«gaussNorm_sum_le» := P2M_GroundTheory_Heights__Heights_GaussNormBasic_gaussNorm_sum_le_df58dd8b246b
