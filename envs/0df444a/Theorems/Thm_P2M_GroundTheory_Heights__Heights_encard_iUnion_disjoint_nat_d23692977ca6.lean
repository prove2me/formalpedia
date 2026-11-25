-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_encard_iUnion_disjoint_nat_d23692977ca6
-- name    : P2M_GroundTheory_Heights__Heights_encard_iUnion_disjoint_nat_d23692977ca6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:24.850196+00:00
-- url     : https://prove2.me/theorems/6f227559-be63-40fe-8316-6f5bc3141947
-- title:
--   P2 M Ground Theory Heights  Heights encard i Union disjoint nat d23692977ca6: P2 M Ground Theory Heights  Heights encard i Union disjoint nat d23692977ca6
-- statement:
--   The P2 M Ground Theory Heights  Heights encard i Union disjoint nat d23692977ca6 construction uses the P2 M Ground Theory Heights  Heights encard i Union disjoint nat d23692977ca6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeAreaFormula.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeAreaFormula.lean#L24-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeGraphCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeAreaFormula
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
open MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_encard_iUnion_disjoint_nat_d23692977ca6 {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Function.onFun Disjoint s)) :
    (((⋃ i, s i).encard : ℕ∞) : ℝ≥0∞) = ∑' i, (((s i).encard : ℕ∞) : ℝ≥0∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«encard_iUnion_disjoint_nat» := P2M_GroundTheory_Heights__Heights_encard_iUnion_disjoint_nat_d23692977ca6
