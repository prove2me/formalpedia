-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__factorization_ff46d0e46406
-- name    : P2M_GroupTheoreticShannonCapacity_MAlpha_M__factorization_ff46d0e46406
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:26:37.190799+00:00
-- url     : https://prove2.me/theorems/4dbeaa74-90c1-4b40-a51f-224fc3dbdac6
-- title:
--   P2 M Group Theoretic Shannon Capacity MAlpha M  factorization ff46d0e46406: P2 M Group Theoretic Shannon Capacity MAlpha M  factorization ff46d0e46406
-- statement:
--   For α ≠ -1: M_α = (R_α + αI)(R_α - I)⁻¹
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L574-L591
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L574-L591

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_MAlpha_M__factorization_ff46d0e46406 (n : ℕ) (α : ℝ) (hα : α ≠ -1) :
    Mα n α = (Rα n α + α • 1) * (Rα n α - 1)⁻¹ := by sorry

alias «GroupTheoreticShannonCapacity».«MAlpha».«Mα_factorization» := P2M_GroupTheoreticShannonCapacity_MAlpha_M__factorization_ff46d0e46406
