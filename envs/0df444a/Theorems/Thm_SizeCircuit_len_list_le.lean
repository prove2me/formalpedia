-- Prove2me | Theorems.Thm_SizeCircuit_len_list_le
-- name    : SizeCircuit.len_list_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:44:10.531547+00:00
-- url     : https://prove2.me/theorems/2712f348-6955-434f-88cd-e7d5890157d8
-- title:
--   Size Circuit: len list le
-- statement:
--   The word of a list of at most L elements with words of length at most B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L78-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L78-L79

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

theorem SizeCircuit.len_list_le {α : Type} [Enc α] {B L : ℕ} {l : List α} (h : ∀ a ∈ l, len a ≤ B) (hL : l.length ≤ L) : len l ≤ L * (B + 2) + 2 := by sorry
