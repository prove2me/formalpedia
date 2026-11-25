-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_exists_ne_zero_1ce62324bc5a
-- name    : P2M_GroundTheory_Heights__Heights_KShort_exists_ne_zero_1ce62324bc5a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:22.603335+00:00
-- url     : https://prove2.me/theorems/819138cd-03a5-4345-b198-1f8b779f0cff
-- title:
--   P2 M Ground Theory Heights  Heights KShort exists ne zero 1ce62324bc5a: P2 M Ground Theory Heights  Heights KShort exists ne zero 1ce62324bc5a
-- statement:
--   The P2 M Ground Theory Heights  Heights KShort exists ne zero 1ce62324bc5a construction uses the P2 M Ground Theory Heights  Heights KShort exists ne zero 1ce62324bc5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L108-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L108-L119

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors
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
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_KShort_exists_ne_zero_1ce62324bc5a (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] : ∃ v ∈ L, v ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KShort».«exists_ne_zero» := P2M_GroundTheory_Heights__Heights_KShort_exists_ne_zero_1ce62324bc5a
