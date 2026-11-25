-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_primeTube_exists_dim_0fd17737f684
-- name    : P2M_GroundTheory_Heights__Heights_primeTube_exists_dim_0fd17737f684
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:50:26.461538+00:00
-- url     : https://prove2.me/theorems/edcde957-9894-4d4b-8d76-3c9767982c13
-- title:
--   P2 M Ground Theory Heights  Heights prime Tube exists dim 0fd17737f684: P2 M Ground Theory Heights  Heights prime Tube exists dim 0fd17737f684
-- statement:
--   The P2 M Ground Theory Heights  Heights prime Tube exists dim 0fd17737f684 construction uses the P2 M Ground Theory Heights  Heights prime Tube exists dim 0fd17737f684 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeTubeVolume.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimeTubeVolume.lean#L26-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyMassLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeTubeVolume
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
open MvPolynomial MeasureTheory ComplexSets Metric
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_primeTube_exists_dim_0fd17737f684 {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (k : ℕ)) :
    ∃ d : ℕ, d ≤ k ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«primeTube_exists_dim» := P2M_GroundTheory_Heights__Heights_primeTube_exists_dim_0fd17737f684
