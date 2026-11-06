-- Prove2me | Theorems.Thm_Sat3Graph_time_mono
-- name    : Sat3Graph.time_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:02:29.194928+00:00
-- url     : https://prove2.me/theorems/3e25b37c-de1f-4eb0-827d-cf7be7d64a76
-- title:
--   Sat3 Graph: time mono
-- statement:
--   c·2^{δn} grows with c and δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L44-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L44-L48

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

theorem Sat3Graph.time_mono {c c' : ℕ} {δ δ' : ℝ} (hδ : δ ≤ δ') (hc : c ≤ c') (n : ℕ) : (c : ℝ) * (2 : ℝ) ^ (δ * n) ≤ c' * (2 : ℝ) ^ (δ' * n) := by sorry
