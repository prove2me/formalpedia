-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_det_xR__add_yI_9d0b1d30422b
-- name    : P2M_GroupTheoreticShannonCapacity_MAlpha_det_xR__add_yI_9d0b1d30422b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:35.139443+00:00
-- url     : https://prove2.me/theorems/2234d636-f5e5-4f1e-ae7f-f575d0701888
-- title:
--   P2 M Group Theoretic Shannon Capacity MAlpha det x R  add y I 9d0b1d30422b: P2 M Group Theoretic Shannon Capacity MAlpha det x R  add y I 9d0b1d30422b
-- statement:
--   det(xR_α + yI) = (-x)ⁿα + yⁿ (for n ≥ 1)
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L117-L238
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L117-L238

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_MAlpha_det_xR__add_yI_9d0b1d30422b (n : ℕ) (hn : 1 ≤ n) (x y α : ℝ) :
    (x • Rα n α + y • 1).det = (-x)^n * α + y^n := by sorry

alias «GroupTheoreticShannonCapacity».«MAlpha».«det_xRα_add_yI» := P2M_GroupTheoreticShannonCapacity_MAlpha_det_xR__add_yI_9d0b1d30422b
