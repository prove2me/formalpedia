-- Prove2me | Theorems.Thm_Sat3Graph_decidesInTime_of_hosted
-- name    : Sat3Graph.decidesInTime_of_hosted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:44:36.675974+00:00
-- url     : https://prove2.me/theorems/a219bff7-dd5a-49f0-9bf6-5bc84d86b0eb
-- title:
--   Sat3 Graph: decides In Time of hosted
-- statement:
--   A property that a hosted decider decides is decided in time O(2^{δn}).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Main.lean#L43-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Main.lean#L43-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_Sat3Graph_Sets
import Definitions.Def_Sat3Graph_Dominating
import Definitions.Def_Sat3Graph_Coloring
import Definitions.Def_Sat3Graph_Cert
import Definitions.Def_Sat3Graph_Host
import Definitions.Def_SizeCircuit_Circuit
import Definitions.Def_SizeCircuit_Cert
import Definitions.Def_Complement_Readers
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_GraphProblems_DomTree
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Main
set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper SizeCircuit Complement SplitSat

theorem Sat3Graph.decidesInTime_of_hosted {Ms : StepMachine (List Bool) Bool} {p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop} {δ : ℝ} (h : HostedFor Ms p δ) :
    DecidesInTime p δ := by sorry
