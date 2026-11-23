-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_R__sub_one_isUnit_29a9b3d1283b
-- name    : P2M_GroupTheoreticShannonCapacity_MAlpha_R__sub_one_isUnit_29a9b3d1283b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:34.303964+00:00
-- url     : https://prove2.me/theorems/2a449750-65dd-4bc7-8a55-d554743ac100
-- title:
--   P2 M Group Theoretic Shannon Capacity MAlpha R  sub one is Unit 29a9b3d1283b: P2 M Group Theoretic Shannon Capacity MAlpha R  sub one is Unit 29a9b3d1283b
-- statement:
--   R_α - I is invertible when α ≠ -1 (using det = (-1)^n(α+1) ≠ 0)
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L243-L259
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L243-L259

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_MAlpha_R__sub_one_isUnit_29a9b3d1283b (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : α ≠ -1) :
    IsUnit (Rα n α - 1) := by sorry

alias «GroupTheoreticShannonCapacity».«MAlpha».«Rα_sub_one_isUnit» := P2M_GroupTheoreticShannonCapacity_MAlpha_R__sub_one_isUnit_29a9b3d1283b
