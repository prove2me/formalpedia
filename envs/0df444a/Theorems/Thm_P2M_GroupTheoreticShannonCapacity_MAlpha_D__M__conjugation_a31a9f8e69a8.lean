-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_D__M__conjugation_a31a9f8e69a8
-- name    : P2M_GroupTheoreticShannonCapacity_MAlpha_D__M__conjugation_a31a9f8e69a8
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:26:43.264268+00:00
-- url     : https://prove2.me/theorems/a0168568-da02-44af-a2a8-af47bf37a344
-- title:
--   P2 M Group Theoretic Shannon Capacity MAlpha D  M  conjugation a31a9f8e69a8: P2 M Group Theoretic Shannon Capacity MAlpha D  M  conjugation a31a9f8e69a8
-- statement:
--   D_β M_α D_β⁻¹ = (β • R_γ + α • I)(β • R_γ - I)⁻¹ where γ = αβ⁻ⁿ
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L782-L833
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/MAlpha.lean#L782-L833

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_MAlpha_D__M__conjugation_a31a9f8e69a8 (n : ℕ) (hn : 1 ≤ n) (α β : ℝ) (hα : α ≠ -1) (hβ : β ≠ 0) :
    Dα n β * Mα n α * (Dα n β)⁻¹ =
    (β • Rα n (α * β⁻¹^n) + α • 1) * (β • Rα n (α * β⁻¹^n) - 1)⁻¹ := by sorry

alias «GroupTheoreticShannonCapacity».«MAlpha».«Dα_Mα_conjugation» := P2M_GroupTheoreticShannonCapacity_MAlpha_D__M__conjugation_a31a9f8e69a8
