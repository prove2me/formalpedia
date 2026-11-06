-- Prove2me | Theorems.Thm_Sat3Graph_decidesColor_mono
-- name    : Sat3Graph.decidesColor_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:53:58.333815+00:00
-- url     : https://prove2.me/theorems/bc07bace-4541-48d0-87f4-00d82a35987a
-- title:
--   Sat3 Graph: decides Color mono
-- statement:
--   `DecidesColor Ms k δ c` stays true when δ and c are made larger.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L58-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Host.lean#L58-L62

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

theorem Sat3Graph.decidesColor_mono {Ms : StepMachine (List Bool) Bool} {k : ℕ} {δ δ' : ℝ} {c c' : ℕ}
    (hδ : δ ≤ δ') (hc : c ≤ c') (h : DecidesColor Ms k δ c) : DecidesColor Ms k δ' c' := by sorry
