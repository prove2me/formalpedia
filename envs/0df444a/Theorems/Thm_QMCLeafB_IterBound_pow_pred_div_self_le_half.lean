-- Prove2me | Theorems.Thm_QMCLeafB_IterBound_pow_pred_div_self_le_half
-- name    : QMCLeafB_IterBound_pow_pred_div_self_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T15:14:36.574753+00:00
-- url     : https://prove2.me/theorems/1f487355-bb4c-430c-90b4-9860ea8a4af6
-- title:
--   Iteration halving factor for ellipsoid potential
-- statement:
--   The elementary estimate $((m-1)/m)^m \le 1/2$ for $m\ge 2$, used to halve the ellipsoid potential every $m$ steps.

import Mathlib
open scoped BigOperators

theorem QMCLeafB_IterBound_pow_pred_div_self_le_half (m : ℕ) (hm : 2 ≤ m) : (((m - 1 : ℕ) : ℚ) / (m : ℚ)) ^ m ≤ 1 / 2 := by sorry
