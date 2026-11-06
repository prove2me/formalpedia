-- Prove2me | Theorems.Thm_SplitSat_stReduceCore
-- name    : SplitSat.stReduceCore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:48:20.838231+00:00
-- url     : https://prove2.me/theorems/bfed37fb-55c3-486d-a87b-618cc871dc5d
-- title:
--   Split Sat: st Reduce Core
-- statement:
--   **The reduction is correct and fast, for every procedure D**, on the tree of the procedure
--   behind the Lean form of Lemma 4, run at width k: the statement `SplitSat.StReduceCore`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Walk.lean#L157-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Walk.lean#L157-L157

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Sizes
import Mathlib.Tactic
import Definitions.Def_SplitSat_Walk
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight.Width

theorem SplitSat.stReduceCore : StReduceCore := by sorry
