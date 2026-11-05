-- Prove2me | Theorems.Thm_PaddedDescent_two_pow_two_pow_sOf_le
-- name    : PaddedDescent.two_pow_two_pow_sOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:13.539498+00:00
-- url     : https://prove2.me/theorems/0fc0460c-b9e4-4f30-b317-e16dc8430fd3
-- title:
--   Padded Descent: two pow two pow s Of le
-- statement:
--   If sOf n ≥ 1 then 2^(2^(depthOf (sOf n) + 211)) ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L96-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L96-L101

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

theorem PaddedDescent.two_pow_two_pow_sOf_le {n : ℕ} (h : 1 ≤ sOf n) : 2 ^ 2 ^ (depthOf (sOf n) + 211) ≤ n := by sorry
