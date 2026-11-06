-- Prove2me | Theorems.Thm_SplitSat_size_unary_le
-- name    : SplitSat.size_unary_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:43:52.172055+00:00
-- url     : https://prove2.me/theorems/89bc9ebc-bdbf-45b6-b247-1b10f6155839
-- title:
--   Split Sat: size unary le
-- statement:
--   n in unary has size at most 2n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L115-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Sizes.lean#L115-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Mathlib.Tactic
import Definitions.Def_SplitSat_Sizes
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify

theorem SplitSat.size_unary_le (n : ℕ) : size (List.replicate n ()) ≤ 2 * n + 1 := by sorry
