-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KShort_pow_le_covolume_f25d525c2258
-- name    : P2M_GroundTheory_Heights__Heights_KShort_pow_le_covolume_f25d525c2258
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:58.446421+00:00
-- url     : https://prove2.me/theorems/e79bb8e8-ddab-4564-8e13-47add7cb5fdd
-- title:
--   P2 M Ground Theory Heights  Heights KShort pow le covolume f25d525c2258: P2 M Ground Theory Heights  Heights KShort pow le covolume f25d525c2258
-- statement:
--   The P2 M Ground Theory Heights  Heights KShort pow le covolume f25d525c2258 construction uses the P2 M Ground Theory Heights  Heights KShort pow le covolume f25d525c2258 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L70-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ShortVectors.lean#L70-L106

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

theorem P2M_GroundTheory_Heights__Heights_KShort_pow_le_covolume_f25d525c2258 (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {lam : ℝ} (hlam : 0 < lam)
    (hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖) :
    (lam / √n) ^ n ≤ ZLattice.covolume L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KShort».«pow_le_covolume» := P2M_GroundTheory_Heights__Heights_KShort_pow_le_covolume_f25d525c2258
