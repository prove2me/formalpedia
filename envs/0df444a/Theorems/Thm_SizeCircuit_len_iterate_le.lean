-- Prove2me | Theorems.Thm_SizeCircuit_len_iterate_le
-- name    : SizeCircuit.len_iterate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:36:31.533431+00:00
-- url     : https://prove2.me/theorems/4df427a5-12c0-4a36-acd9-ea4a8e0bd613
-- title:
--   Size Circuit: len iterate le
-- statement:
--   After k ≤ n steps the word of the state has length at most `stateLen m`, for every m ≥ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L117-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L117-L128

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
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.len_iterate_le (n k m : ℕ) (hk : k ≤ n) (hm : n ≤ m) : len ((addStep n)^[k] (addStart n)) ≤ stateLen m := by sorry
