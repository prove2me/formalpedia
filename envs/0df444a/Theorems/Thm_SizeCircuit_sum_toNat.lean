-- Prove2me | Theorems.Thm_SizeCircuit_sum_toNat
-- name    : SizeCircuit.sum_toNat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:38:00.18241+00:00
-- url     : https://prove2.me/theorems/5cd2620d-3b01-4962-9c37-756d582b5ac9
-- title:
--   Size Circuit: sum to Nat
-- statement:
--   The sum of the bits of a word is the number of its ones.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Circuit.lean#L29-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Circuit.lean#L29-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_General
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_SizeCircuit_Compare
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Circuit
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.sum_toNat (x : List Bool) : (x.map Bool.toNat).sum = x.count true := by sorry
