-- Prove2me | Theorems.Thm_SplitCount_stStepThree
-- name    : SplitCount.stStepThree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:47:01.553129+00:00
-- url     : https://prove2.me/theorems/55259326-7d43-4c18-9723-a71e77f9e45a
-- title:
--   Split Count: st Step Three
-- statement:
--   **The width reduction of Corollary 6**, for the program: on Ψ on x₀ … xₙ₋₁ with m clauses of ≤ w
--   literals, `widthP` gives (n₃ in unary, Ψ₃): ≤ 3 literals per clause, variables below n₃, no clause
--   twice, n₃ ≤ n + (w−3)·m, ≤ m + 3(w−3)·m clauses, and as many satisfying assignments on n₃ variables
--   as Ψ on n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Width.lean#L35-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Width.lean#L35-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_Occ_Main
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_SplitCount_Width
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat Eight.Width Occ

theorem SplitCount.stStepThree : StStepThree := by sorry
