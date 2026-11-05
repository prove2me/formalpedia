-- Prove2me | Theorems.Thm_PaddedDescent_overhead_mul_le
-- name    : PaddedDescent.overhead_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:32:49.791724+00:00
-- url     : https://prove2.me/theorems/4336e438-09a3-4530-8bfa-5378172b28bd
-- title:
--   Padded Descent: overhead mul le
-- statement:
--   If n ≥ Y^(2a+2) then an overhead W ≤ c·Y^a·(⌊√n⌋+1), with c ≤ 2^500, satisfies W·2^s ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L48-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L48-L68

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

theorem PaddedDescent.overhead_mul_le {s n W a c : ℕ} (hc : c ≤ 2 ^ 500) (hn : Ytop s ^ (2 * a + 2) ≤ n)
    (hW : W ≤ c * Ytop s ^ a * (Nat.sqrt n + 1)) : W * 2 ^ s ≤ n := by sorry
