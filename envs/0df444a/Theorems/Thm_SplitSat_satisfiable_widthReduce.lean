-- Prove2me | Theorems.Thm_SplitSat_satisfiable_widthReduce
-- name    : SplitSat.satisfiable_widthReduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:34:26.522569+00:00
-- url     : https://prove2.me/theorems/67cb3e44-5fb6-4706-802c-662a5a2cf0f9
-- title:
--   Split Sat: satisfiable width Reduce
-- statement:
--   The formula with its long clauses split is satisfiable exactly if the formula is: one direction
--   restricts an assignment to the old variables, the other extends it to the new ones.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Leaf.lean#L57-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Leaf.lean#L57-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_GraphProblems_Engine
import Mathlib.Tactic
import Definitions.Def_SplitSat_Leaf
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Eight.Width GraphProblems

theorem SplitSat.satisfiable_widthReduce {n : ℕ} (φ : Sat3.CNF n) : Sat3.Satisfiable (widthReduce φ) ↔ Sat3.Satisfiable φ := by sorry
