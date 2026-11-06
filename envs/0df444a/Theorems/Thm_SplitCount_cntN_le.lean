-- Prove2me | Theorems.Thm_SplitCount_cntN_le
-- name    : SplitCount.cntN_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:35:48.220506+00:00
-- url     : https://prove2.me/theorems/dbad039d-f119-4de0-a3e8-df027f09db13
-- title:
--   Split Count: cnt N le
-- statement:
--   There are at most 2^n satisfying assignments on x₀ … xₙ₋₁.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L77-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L77-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
import Theorems.Thm_GraphProblems_cntN_le

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat

theorem SplitCount.cntN_le (n : ℕ) (x : Fml) : cntN n x ≤ 2 ^ n := by sorry
