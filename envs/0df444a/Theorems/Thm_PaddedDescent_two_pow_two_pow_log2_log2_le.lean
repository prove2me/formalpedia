-- Prove2me | Theorems.Thm_PaddedDescent_two_pow_two_pow_log2_log2_le
-- name    : PaddedDescent.two_pow_two_pow_log2_log2_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:32:40.91834+00:00
-- url     : https://prove2.me/theorems/053c407e-4dac-4d91-853b-d536e5633b38
-- title:
--   Padded Descent: two pow two pow log2 log2 le
-- statement:
--   2^(2^⌊log₂⌊log₂ n⌋⌋) ≤ n as soon as n ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L87-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L87-L89

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

theorem PaddedDescent.two_pow_two_pow_log2_log2_le {n : ℕ} (h : Nat.log2 n ≠ 0) : 2 ^ 2 ^ Nat.log2 (Nat.log2 n) ≤ n := by sorry
