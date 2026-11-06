-- Prove2me | Theorems.Thm_Sat3Graph_size_mono
-- name    : Sat3Graph.size_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:52:36.886797+00:00
-- url     : https://prove2.me/theorems/c3adffb2-5364-430f-9b9f-5793c42ee17d
-- title:
--   Sat3 Graph: size mono
-- statement:
--   c·(n+2)^c grows with c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L40-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L40-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_GraphProblems_Read
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Host
set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog GraphProblems Paper SplitSat

theorem Sat3Graph.size_mono {c c' : ℕ} (hc : c ≤ c') (n : ℕ) : c * (n + 2) ^ c ≤ c' * (n + 2) ^ c' := by sorry
