-- Prove2me | Theorems.Thm_SplitCount_size_unary
-- name    : SplitCount.size_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:35:54.653487+00:00
-- url     : https://prove2.me/theorems/926513b5-356e-486a-87b4-17d31d940342
-- title:
--   Split Count: size unary
-- statement:
--   The size of n in unary is at most 2n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L55-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L55-L56

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

theorem SplitCount.size_unary (n : ℕ) : size (List.replicate n ()) ≤ n * 2 + 1 := by sorry
