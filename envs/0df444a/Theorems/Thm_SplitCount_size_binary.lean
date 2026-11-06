-- Prove2me | Theorems.Thm_SplitCount_size_binary
-- name    : SplitCount.size_binary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:32:45.661837+00:00
-- url     : https://prove2.me/theorems/2539dfc3-2c45-4995-b2be-8e5cac983773
-- title:
--   Split Count: size binary
-- statement:
--   The size of a word of n + 1 bits is at most 2(n+1) + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L59-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L59-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat

theorem SplitCount.size_binary (n v : ℕ) : size (SatK.binary n v) ≤ (n + 1) * 2 + 1 := by sorry
