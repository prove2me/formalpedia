-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__principalSubmatrix_9b037532404d
-- name    : P2M_GroupTheoreticShannonCapacity_MAlpha_M__principalSubmatrix_9b037532404d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:32:17.02345+00:00
-- url     : https://prove2.me/theorems/312ed88c-1db5-4666-a89c-40ffb0f5cd9d
-- title:
--   P2 M Group Theoretic Shannon Capacity MAlpha M  principal Submatrix 9b037532404d: P2 M Group Theoretic Shannon Capacity MAlpha M  principal Submatrix 9b037532404d
-- statement:
--   Principal submatrices of M_α are M_α matrices of smaller size.
--       The key insight: M_α structure only depends on relative ordering of indices.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L672-L694
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L672-L694

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_MAlpha_M__principalSubmatrix_9b037532404d (n : ℕ) (α : ℝ) (S : Finset (Fin n)) :
    P0Matrix.principalSubmatrix n (Mα n α) S = Mα S.card α := by sorry

alias «GroupTheoreticShannonCapacity».«MAlpha».«Mα_principalSubmatrix» := P2M_GroupTheoreticShannonCapacity_MAlpha_M__principalSubmatrix_9b037532404d
