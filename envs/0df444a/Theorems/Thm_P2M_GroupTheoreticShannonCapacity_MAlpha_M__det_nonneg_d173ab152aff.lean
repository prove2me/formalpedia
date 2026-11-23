-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_nonneg_d173ab152aff
-- name    : P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_nonneg_d173ab152aff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:04.93486+00:00
-- url     : https://prove2.me/theorems/4838ae5d-526e-434f-a3d9-2b881677cec9
-- title:
--   P2 M Group Theoretic Shannon Capacity MAlpha M  det nonneg d173ab152aff: P2 M Group Theoretic Shannon Capacity MAlpha M  det nonneg d173ab152aff
-- statement:
--   For α ∈ [0,1], det(M_α) ≥ 0
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L619-L666
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L619-L666

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_nonneg_d173ab152aff (n : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    (Mα n α).det ≥ 0 := by sorry

alias «GroupTheoreticShannonCapacity».«MAlpha».«Mα_det_nonneg» := P2M_GroupTheoreticShannonCapacity_MAlpha_M__det_nonneg_d173ab152aff
