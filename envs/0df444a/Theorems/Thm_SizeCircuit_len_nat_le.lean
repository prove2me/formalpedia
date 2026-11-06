-- Prove2me | Theorems.Thm_SizeCircuit_len_nat_le
-- name    : SizeCircuit.len_nat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:54:09.774414+00:00
-- url     : https://prove2.me/theorems/277efb83-7ec9-4150-87a1-b988b7d28061
-- title:
--   Size Circuit: len nat le
-- statement:
--   The word of a number x ≤ M has length at most 3M + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L82-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L82-L85

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

theorem SizeCircuit.len_nat_le {x M : ℕ} (h : x ≤ M) : len x ≤ 3 * M + 2 := by sorry
