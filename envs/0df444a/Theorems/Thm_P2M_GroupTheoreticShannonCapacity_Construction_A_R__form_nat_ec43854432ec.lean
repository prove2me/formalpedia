-- Prove2me | Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_nat_ec43854432ec
-- name    : P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_nat_ec43854432ec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:34:11.50439+00:00
-- url     : https://prove2.me/theorems/7e84e2ed-dd00-423b-aa9a-40b8e8bdace4
-- title:
--   P2 M Group Theoretic Shannon Capacity Construction A R  form nat ec43854432ec: P2 M Group Theoretic Shannon Capacity Construction A R  form nat ec43854432ec
-- statement:
--   A in R_α form for natural number parameters:
--       A = (p·R_{r/k} - pb·I) · (s·R_{r/k} - a·I)⁻¹
--
--       **Derivation** using Mα_conjugation:
--       1. From X_factorization: X = (ka^{n-1}/s)·D_{s/a}·M_α·D_{a/s} where α = rs^n/(ka^n)
--       2. So A = qI + X = qI + (ka^{n-1}/s)·D_{s/a}·M_α·D_{a/s}
--       3. Apply Mα_conjugation with x=q, y=ka^{n-1}/s, β=s/a:
--          - γ = αβ^{-n} = r/k
--          - β(x+y) = (s/a)(q + ka^{n-1}/s) = p/a  (using p = qs + ka^{n-1})
--          - -x + yα = -q + rs^{n-1}/a = (rs^{n-1} - qa)/a = -pb/a  (using pb = qa - rs^{n-1})
--       4. Result: A = (p/a·R_{r/k} - pb/a·I) · ((s/a)·R_{r/k} - I)⁻¹
--                = (p·R_{r/k} - pb·I) · (s·R_{r/k} - a·I)⁻¹  (scaling by a)
--
--   Source: https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1252-L1441
-- source:
--   https://github.com/jzuiddam/GroupTheoreticShannonCapacity/blob/b3293c2c912c08768684ea560f3a59afe59920b1/GroupTheoreticShannonCapacity/Construction.lean#L1252-L1441

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix

theorem P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_nat_ec43854432ec (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b) (hs : 1 ≤ s)
    (hn_num : (s : ℤ) ^ n * (r : ℤ) + (k : ℤ) * (a n (k : ℤ) (b : ℤ) (r : ℤ) (s : ℤ)) ^ n ≠ 0) :
    let R := MAlpha.Rα n ((r : ℝ) / (k : ℝ))
    (matrixA n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ) =
    ((p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) • R - (p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) * (b:ℤ) : ℝ) • 1) *
    ((s : ℝ) • R - (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) • 1)⁻¹ := by sorry

alias «GroupTheoreticShannonCapacity».«Construction».«A_Rα_form_nat» := P2M_GroupTheoreticShannonCapacity_Construction_A_R__form_nat_ec43854432ec
