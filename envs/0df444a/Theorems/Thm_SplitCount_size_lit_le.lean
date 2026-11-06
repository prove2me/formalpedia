-- Prove2me | Theorems.Thm_SplitCount_size_lit_le
-- name    : SplitCount.size_lit_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:32:42.345848+00:00
-- url     : https://prove2.me/theorems/4cf63aa8-ae3a-4959-a593-70933efffd62
-- title:
--   Split Count: size lit le
-- statement:
--   A literal on a variable below n has size at most n + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L44-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L44-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
import Theorems.Thm_Groundwork_Prog_size_lit_le

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat

theorem SplitCount.size_lit_le {l : ℕ × Bool} {n : ℕ} (h : l.1 < n) : size l ≤ n + 2 := by sorry
