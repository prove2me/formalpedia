-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_exists_isLeast_a128e7cb936c
-- name    : P2M_GroundTheory_Heights__Heights_KShort_exists_isLeast_a128e7cb936c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:17.298511+00:00
-- url     : https://prove2.me/theorems/b3fe7be8-a54b-48df-a4d1-387e274f8447
-- title:
--   P2 M Ground Theory Heights  Heights KShort exists is Least a128e7cb936c: P2 M Ground Theory Heights  Heights KShort exists is Least a128e7cb936c
-- statement:
--   The P2 M Ground Theory Heights  Heights KShort exists is Least a128e7cb936c construction uses the P2 M Ground Theory Heights  Heights KShort exists is Least a128e7cb936c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L130-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L130-L144

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

theorem P2M_GroundTheory_Heights__Heights_KShort_exists_isLeast_a128e7cb936c (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ lam : ℝ, 0 < lam ∧ IsLeast {t | ∃ v ∈ L, v ≠ 0 ∧ t = ‖v‖} lam := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KShort».«exists_isLeast» := P2M_GroundTheory_Heights__Heights_KShort_exists_isLeast_a128e7cb936c
