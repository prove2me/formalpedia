-- Prove2me | Theorems.Thm_SplitCount_size_nat_le
-- name    : SplitCount.size_nat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:38:52.576586+00:00
-- url     : https://prove2.me/theorems/a6f07c73-d4ee-4562-91ea-7c193b6ed4fc
-- title:
--   Split Count: size nat le
-- statement:
--   A number below 2^B has size at most B + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L63-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L63-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
import Theorems.Thm_Groundwork_Prog_size_nat_le

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat

theorem SplitCount.size_nat_le {v B : ℕ} (h : v < 2 ^ B) : size v ≤ B + 1 := by sorry
