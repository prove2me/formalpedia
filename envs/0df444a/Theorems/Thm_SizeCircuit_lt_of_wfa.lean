-- Prove2me | Theorems.Thm_SizeCircuit_lt_of_wfa
-- name    : SizeCircuit.lt_of_wfa
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:38:18.928092+00:00
-- url     : https://prove2.me/theorems/7d3b8ea9-a31f-4196-836e-309caf2fa979
-- title:
--   Size Circuit: lt of wfa
-- statement:
--   Gates that read earlier wires only name wires below the number of all wires.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L97-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L97-L106

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Cert
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.lt_of_wfa : ∀ {K : List GateD} {n : ℕ}, WFa n K → ∀ g ∈ K, g.2.1 < n + K.length ∧ g.2.2 < n + K.length
  := by sorry
