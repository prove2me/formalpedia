-- Prove2me | Theorems.Thm_SplitCount_holds_addP
-- name    : SplitCount.holds_addP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:57:18.307911+00:00
-- url     : https://prove2.me/theorems/b2ab9f33-408c-4fc5-8202-cc42337b578e
-- title:
--   Split Count: holds add P
-- statement:
--   `addP A s` holds exactly if A and s hold: a clause that `addP` drops contains a clause of A.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L35-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Disjoint.lean#L35-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Disjoint
import Theorems.Thm_CountKSat_StepCount_holds_addP

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight.Width

theorem SplitCount.holds_addP (b : ℕ → Bool) (A s : PFml) : Holds b (addP A s) ↔ Holds b A ∧ Holds b s := by sorry
