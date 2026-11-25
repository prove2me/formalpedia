-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisS_spec_d0b72175b660
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisS_spec_d0b72175b660
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:37.934029+00:00
-- url     : https://prove2.me/theorems/c3de4bb9-6a92-51be-8116-eb908d3c0db1
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis S spec d0b72175b660: P2 M Ground Theory Heights  Heights Finite Covolume heis S spec d0b72175b660
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis S spec d0b72175b660 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis S spec d0b72175b660 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean#L106-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
variable {H : Matrix ι ι ℂ}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisS_spec_d0b72175b660 (hH : H.IsHermitian) (y : ι → ℂ) (t : ℝ) :
    heisS H y t + starRingEnd ℂ (heisS H y t) + hForm H y y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisS_spec» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisS_spec_d0b72175b660
