-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__isP0_c8d2d6fe8993
-- name    : P2M_GroupTheoreticShannonCapacity_MAlpha_M__isP0_c8d2d6fe8993
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:26:36.799134+00:00
-- url     : https://prove2.me/theorems/179269a4-0942-4f12-a082-2b92be18827d
-- title:
--   P2 M Group Theoretic Shannon Capacity MAlpha M  is P0 c8d2d6fe8993: P2 M Group Theoretic Shannon Capacity MAlpha M  is P0 c8d2d6fe8993
-- statement:
--   For α ∈ [0, 1], M_α is a P₀-matrix
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L697-L701
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L697-L701

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_MAlpha_M__isP0_c8d2d6fe8993 (n : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    P0Matrix.IsP0Matrix n (Mα n α) := by sorry

alias «GroupTheoreticShannonCapacity».«MAlpha».«Mα_isP0» := P2M_GroupTheoreticShannonCapacity_MAlpha_M__isP0_c8d2d6fe8993
