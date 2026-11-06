-- Prove2me | Theorems.Thm_SizeCircuit_obeys_unique
-- name    : SizeCircuit.obeys_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:23:12.966968+00:00
-- url     : https://prove2.me/theorems/8f299d74-8a1d-44bb-9979-ffa76be9f785
-- title:
--   Size Circuit: obeys unique
-- statement:
--   Two assignments that obey a circuit whose gates read earlier wires only, and agree on the wires
--   below n, agree on the wires of all gates.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L114-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L114-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_General
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.obeys_unique {a a' : ℕ → Bool} : ∀ {K : List GateD} {n : ℕ}, WFa n K → Obeys a n K → Obeys a' n K → (∀ i < n, a i = a' i) →
    ∀ i < n + K.length, a i = a' i
  := by sorry
