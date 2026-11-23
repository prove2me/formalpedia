-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_72ab166505ea
-- name    : P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_72ab166505ea
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:40.633078+00:00
-- url     : https://prove2.me/theorems/d3bac60e-0be2-4f32-9a0a-d3b8759e9181
-- title:
--   P2 M Group Theoretic Shannon Capacity MAlpha M  det 72ab166505ea: P2 M Group Theoretic Shannon Capacity MAlpha M  det 72ab166505ea
-- statement:
--   det(M_α) for n ≥ 1: uses the factorization M_α = (R_α + αI)(R_α - I)⁻¹
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L598-L616
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L598-L616

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_72ab166505ea (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : α ≠ -1) :
    (Mα n α).det = ((-1)^n * α + α^n) / ((-1)^n * α + (-1)^n) := by sorry

alias «GroupTheoreticShannonCapacity».«MAlpha».«Mα_det» := P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_72ab166505ea
