-- Prove2me | Theorems.Thm_PaddedDescent_overhead_sOf_le_div
-- name    : PaddedDescent.overhead_sOf_le_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:42:27.852315+00:00
-- url     : https://prove2.me/theorems/add31a39-9f2e-4de7-87ed-ef4894e91335
-- title:
--   Padded Descent: overhead s Of le div
-- statement:
--   The threshold and the choice of s together: if sOf n ≥ 1 then an overhead W ≤ c·Y^a·(⌊√n⌋+1),
--   with Y = Ytop (sOf n), c ≤ 2^500 and
--   2a + 2 ≤ 2^200, is at most ⌊n/2^(sOf n)⌋.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L110-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L110-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_Threshold
set_option autoImplicit false
section
section
open PaddedDescent

theorem PaddedDescent.overhead_sOf_le_div {n W a c : ℕ} (h : 1 ≤ sOf n) (ha : 2 * a + 2 ≤ 2 ^ 200) (hc : c ≤ 2 ^ 500)
    (hW : W ≤ c * Ytop (sOf n) ^ a * (Nat.sqrt n + 1)) : W ≤ n / 2 ^ sOf n := by sorry
