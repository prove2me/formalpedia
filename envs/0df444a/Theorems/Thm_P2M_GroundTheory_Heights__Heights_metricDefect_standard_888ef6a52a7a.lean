-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_metricDefect_standard_888ef6a52a7a
-- name    : P2M_GroundTheory_Heights__Heights_metricDefect_standard_888ef6a52a7a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:57.7078+00:00
-- url     : https://prove2.me/theorems/661addbe-d66d-4ac7-aa1e-324b1ba56b28
-- title:
--   P2 M Ground Theory Heights  Heights metric Defect standard 888ef6a52a7a: P2 M Ground Theory Heights  Heights metric Defect standard 888ef6a52a7a
-- statement:
--   The P2 M Ground Theory Heights  Heights metric Defect standard 888ef6a52a7a construction uses the P2 M Ground Theory Heights  Heights metric Defect standard 888ef6a52a7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Comparison.lean#L86-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_metricDefect_standard_888ef6a52a7a [Fintype ι] (z : Cone n ℂ) (hz : BlockNonzero z) :
    metricDefect (HermLine.standard n) z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«metricDefect_standard» := P2M_GroundTheory_Heights__Heights_metricDefect_standard_888ef6a52a7a
