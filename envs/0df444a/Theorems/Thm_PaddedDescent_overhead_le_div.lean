-- Prove2me | Theorems.Thm_PaddedDescent_overhead_le_div
-- name    : PaddedDescent.overhead_le_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:07:27.418301+00:00
-- url     : https://prove2.me/theorems/37cb1841-d907-459f-a9db-8648ee9a50bd
-- title:
--   Padded Descent: overhead le div
-- statement:
--   The same with the division: W ≤ ⌊n/2^s⌋.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L71-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L71-L73

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

theorem PaddedDescent.overhead_le_div {s n W a c : ℕ} (hc : c ≤ 2 ^ 500) (hn : Ytop s ^ (2 * a + 2) ≤ n)
    (hW : W ≤ c * Ytop s ^ a * (Nat.sqrt n + 1)) : W ≤ n / 2 ^ s := by sorry
