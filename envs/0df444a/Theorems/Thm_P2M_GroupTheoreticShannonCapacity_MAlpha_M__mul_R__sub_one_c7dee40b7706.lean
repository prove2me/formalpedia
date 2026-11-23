-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__mul_R__sub_one_c7dee40b7706
-- name    : P2M_GroupTheoreticShannonCapacity_MAlpha_M__mul_R__sub_one_c7dee40b7706
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:31:38.018818+00:00
-- url     : https://prove2.me/theorems/4957561a-6238-4e3c-b57d-492222efa1c4
-- title:
--   P2 M Group Theoretic Shannon Capacity MAlpha M  mul R  sub one c7dee40b7706: P2 M Group Theoretic Shannon Capacity MAlpha M  mul R  sub one c7dee40b7706
-- statement:
--   M_α * (R_α - I) = R_α + αI (the key product identity)
--
--   This is Lemma 3.4 from the paper: the product M_α · (R_α - I) equals R_α + αI.
--   The proof is a direct entry-by-entry computation showing that for each (i,j):
--   - Diagonal entries (i = j): sum equals α
--   - Subdiagonal entries (i = j+1): sum equals 1
--   - Top-right corner (i = 0, j = n-1): sum equals -α
--   - All other entries: sum equals 0
--
--   The key insight is that M_α has α above diagonal, -1 below, 0 on diagonal,
--   and R_α has -α at corner (0, n-1), 1 on subdiagonal, 0 elsewhere.
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L537-L571
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L537-L571

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_MAlpha_M__mul_R__sub_one_c7dee40b7706 (n : ℕ) (α : ℝ) :
    Mα n α * (Rα n α - 1) = Rα n α + α • 1 := by sorry

alias «GroupTheoreticShannonCapacity».«MAlpha».«Mα_mul_Rα_sub_one» := P2M_GroupTheoreticShannonCapacity_MAlpha_M__mul_R__sub_one_c7dee40b7706
