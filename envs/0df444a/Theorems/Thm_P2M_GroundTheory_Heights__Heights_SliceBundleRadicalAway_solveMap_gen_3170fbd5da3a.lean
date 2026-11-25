-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_solveMap_gen_3170fbd5da3a
-- name    : P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_solveMap_gen_3170fbd5da3a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:01.538387+00:00
-- url     : https://prove2.me/theorems/b7a6eeb7-0d66-51e7-8ffc-177fc2d8b5bd
-- title:
--   P2 M Ground Theory Heights  Heights Slice Bundle Radical Away solve Map gen 3170fbd5da3a: P2 M Ground Theory Heights  Heights Slice Bundle Radical Away solve Map gen 3170fbd5da3a
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Bundle Radical Away solve Map gen 3170fbd5da3a construction uses the P2 M Ground Theory Heights  Heights Slice Bundle Radical Away solve Map gen 3170fbd5da3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L106-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean#L106-L128

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

theorem P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_solveMap_gen_3170fbd5da3a (i : Fin d) :
    solveMap J d q k (∑ j, C (X (i, j)) * (X j - C (C (q j)))) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceBundleRadicalAway».«solveMap_gen» := P2M_GroundTheory_Heights__Heights_SliceBundleRadicalAway_solveMap_gen_3170fbd5da3a
