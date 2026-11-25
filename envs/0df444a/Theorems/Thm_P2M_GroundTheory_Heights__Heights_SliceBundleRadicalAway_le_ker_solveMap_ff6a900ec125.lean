-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_le_ker_solveMap_ff6a900ec125
-- name    : P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_le_ker_solveMap_ff6a900ec125
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:16.937175+00:00
-- url     : https://prove2.me/theorems/2d7dea43-7aa6-44d8-92ea-27b0db253ac3
-- title:
--   P2 M Ground Theory Heights  Heights Slice Bundle Radical Away le ker solve Map ff6a900ec125: P2 M Ground Theory Heights  Heights Slice Bundle Radical Away le ker solve Map ff6a900ec125
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Bundle Radical Away le ker solve Map ff6a900ec125 construction uses the P2 M Ground Theory Heights  Heights Slice Bundle Radical Away le ker solve Map ff6a900ec125 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L130-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L130-L138

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBundleRadicalAway
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
open GroundTheory.Heights₂.Heights.SliceBundleRadicalAway
variable {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) (k : Fin n)

theorem P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_le_ker_solveMap_ff6a900ec125 : universalSliceIdeal J d q ≤ RingHom.ker (solveMap J d q k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceBundleRadicalAway».«le_ker_solveMap» := P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_le_ker_solveMap_ff6a900ec125
