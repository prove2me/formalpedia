-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_431fdefa9c23
-- name    : P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_431fdefa9c23
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:34:17.231396+00:00
-- url     : https://prove2.me/theorems/e46fde3a-7c37-47f0-89ec-c742042bd154
-- title:
--   P2 M Group Theoretic Shannon Capacity Construction A R  form 431fdefa9c23: P2 M Group Theoretic Shannon Capacity Construction A R  form 431fdefa9c23
-- statement:
--   A in R_α form: A = (p·R_{r/k} - pb·I) · (s·R_{r/k} - a·I)⁻¹
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1444-L1478
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1444-L1478

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_431fdefa9c23 (n : ℕ) (k b r s : ℤ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hs_pos : 1 ≤ s) (hr : 0 ≤ r)
    (hn_num : s ^ n * r + k * (a n k b r s) ^ n ≠ 0) :
    let α := (r : ℚ) / (k : ℚ)
    let R := MAlpha.Rα n (α : ℝ)
    (matrixA n k b r s).map (↑· : ℚ → ℝ) =
    ((p n k b r s : ℝ) • R - (p n k b r s * b : ℝ) • 1) *
    ((s : ℝ) • R - (a n k b r s : ℝ) • 1)⁻¹ := by sorry

alias «GroupTheoreticShannonCapacity».«Construction».«A_Rα_form» := P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_431fdefa9c23
