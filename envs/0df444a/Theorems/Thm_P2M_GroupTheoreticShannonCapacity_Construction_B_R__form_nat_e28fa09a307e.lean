-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_nat_e28fa09a307e
-- name    : P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_nat_e28fa09a307e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:27:19.366157+00:00
-- url     : https://prove2.me/theorems/57d27514-8749-49ba-abd6-ade1d4c84f56
-- title:
--   P2 M Group Theoretic Shannon Capacity Construction B R  form nat e28fa09a307e: P2 M Group Theoretic Shannon Capacity Construction B R  form nat e28fa09a307e
-- statement:
--   B in R_α form for natural number parameters
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1063-L1208
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1063-L1208

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_nat_e28fa09a307e (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hd : (r : ℤ) + (k : ℤ) * (b : ℤ) ^ n ≠ 0) :
    let R := MAlpha.Rα n ((r : ℝ) / (k : ℝ))
    (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ) =
    ((s : ℝ) • R - (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) • 1) *
    (R - (b : ℝ) • 1)⁻¹ := by sorry

alias «GroupTheoreticShannonCapacity».«Construction».«B_Rα_form_nat» := P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_nat_e28fa09a307e
