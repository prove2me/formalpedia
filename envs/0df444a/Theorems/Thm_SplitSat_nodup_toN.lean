-- Prove2me | Theorems.Thm_SplitSat_nodup_toN
-- name    : SplitSat.nodup_toN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:35:21.169029+00:00
-- url     : https://prove2.me/theorems/57070bfa-2908-4053-99d3-a2e9c4364028
-- title:
--   Split Sat: nodup to N
-- statement:
--   A formula in which no clause is written twice stays so when its variables are read as numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Leaf.lean#L41-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Leaf.lean#L41-L44

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

theorem SplitSat.nodup_toN {n : ℕ} {φ : Sat3.CNF n} (h : φ.Nodup) : (Decode.toN φ).Nodup := by sorry
