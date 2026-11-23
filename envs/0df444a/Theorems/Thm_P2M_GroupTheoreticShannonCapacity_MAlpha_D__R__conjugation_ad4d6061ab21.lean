-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_D__R__conjugation_ad4d6061ab21
-- name    : P2M_GroupTheoreticShannonCapacity_MAlpha_D__R__conjugation_ad4d6061ab21
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:18.789993+00:00
-- url     : https://prove2.me/theorems/569e942f-6fe6-407a-a8a8-3e59d230e329
-- title:
--   P2 M Group Theoretic Shannon Capacity MAlpha D  R  conjugation ad4d6061ab21: P2 M Group Theoretic Shannon Capacity MAlpha D  R  conjugation ad4d6061ab21
-- statement:
--   D_β R_α D_β⁻¹ = β • R_{αβ⁻ⁿ} (direct computation)
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L725-L779
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L725-L779

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_MAlpha_D__R__conjugation_ad4d6061ab21 (n : ℕ) (α β : ℝ) (hβ : β ≠ 0) :
    Dα n β * Rα n α * (Dα n β)⁻¹ = β • Rα n (α * β⁻¹^n) := by sorry

alias «GroupTheoreticShannonCapacity».«MAlpha».«Dα_Rα_conjugation» := P2M_GroupTheoreticShannonCapacity_MAlpha_D__R__conjugation_ad4d6061ab21
