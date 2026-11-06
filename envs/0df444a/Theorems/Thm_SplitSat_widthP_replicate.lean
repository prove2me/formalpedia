-- Prove2me | Theorems.Thm_SplitSat_widthP_replicate
-- name    : SplitSat.widthP_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:35:39.721656+00:00
-- url     : https://prove2.me/theorems/727adb5b-bee0-47a8-b682-55d73a6697e7
-- title:
--   Split Sat: width P replicate
-- statement:
--   The program on (n in unary, x), written out: n + (number of new variables) in unary, and the
--   formula with its long clauses split.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Leaf.lean#L33-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Leaf.lean#L33-L34

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

theorem SplitSat.widthP_replicate (n : ℕ) (x : Fml) : widthP (List.replicate n (), x) = (List.replicate (n + numFresh x) (), splitN n x) := by sorry
