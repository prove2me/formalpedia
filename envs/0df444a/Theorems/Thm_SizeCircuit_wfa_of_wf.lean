-- Prove2me | Theorems.Thm_SizeCircuit_wfa_of_wf
-- name    : SizeCircuit.wfa_of_wf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:38:12.279408+00:00
-- url     : https://prove2.me/theorems/f2f36802-36fe-43aa-bdd4-37798a825fc0
-- title:
--   Size Circuit: wfa of wf
-- statement:
--   If every gate reads earlier wires only, counted by its place in the list (`WF`), then also
--   counted gate by gate (`WFa`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L105-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L105-L110

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_General
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.wfa_of_wf : ∀ {K : List GateD} {n : ℕ}, WF n K → WFa n K
  := by sorry
