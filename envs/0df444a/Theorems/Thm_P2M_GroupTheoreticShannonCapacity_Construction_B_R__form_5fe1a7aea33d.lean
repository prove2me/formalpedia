-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_5fe1a7aea33d
-- name    : P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_5fe1a7aea33d
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:34:15.812344+00:00
-- url     : https://prove2.me/theorems/02f69585-09fb-4d4e-bffc-e13ff911fa10
-- title:
--   P2 M Group Theoretic Shannon Capacity Construction B R  form 5fe1a7aea33d: P2 M Group Theoretic Shannon Capacity Construction B R  form 5fe1a7aea33d
-- statement:
--   B in R_α form: B = (s·R_{r/k} - a·I) · (R_{r/k} - b·I)⁻¹
--
--       **Derivation** using Mα_conjugation:
--       1. From Y_factorization: Y = -kb^{n-1}·D_{1/b}·M_β·D_b where β = r/(kb^n)
--       2. So B = ((a-r)/b)I + Y = ((a-r)/b)I - kb^{n-1}·D_{1/b}·M_β·D_b
--       3. Apply Mα_conjugation with x=(a-r)/b, y=-kb^{n-1}, β'=1/b:
--          - γ = β·(β')^{-n} = r/k
--          - β'(x+y) = (1/b)((a-r)/b - kb^{n-1}) = s/b  (using a = kb^n + sb + r)
--          - -x + yα = -(a-r)/b - r/b = -a/b
--       4. Result: B = (s/b·R_{r/k} - a/b·I) · ((1/b)·R_{r/k} - I)⁻¹
--                = (s·R_{r/k} - a·I) · (R_{r/k} - b·I)⁻¹  (scaling by b)
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1491-L1517
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1491-L1517

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_5fe1a7aea33d (n : ℕ) (k b r s : ℤ) (hn : 1 ≤ n) (hd : r + k * b ^ n ≠ 0)
    (hk : 1 ≤ k) (hb_pos : 1 ≤ b) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    let α := (r : ℚ) / (k : ℚ)
    let R := MAlpha.Rα n (α : ℝ)
    (matrixB n k b r s).map (↑· : ℚ → ℝ) =
    ((s : ℝ) • R - (a n k b r s : ℝ) • 1) *
    (R - (b : ℝ) • 1)⁻¹ := by sorry

alias «GroupTheoreticShannonCapacity».«Construction».«B_Rα_form» := P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_5fe1a7aea33d
