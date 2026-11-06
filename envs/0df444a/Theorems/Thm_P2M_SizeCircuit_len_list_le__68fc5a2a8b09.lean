-- Prove2me | Theorems.Thm_P2M_SizeCircuit_len_list_le__68fc5a2a8b09
-- name    : P2M_SizeCircuit_len_list_le__68fc5a2a8b09
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:37:16.716514+00:00
-- url     : https://prove2.me/theorems/59474db0-9067-4fb2-9ed3-139881091e37
-- title:
--   P2 M Size Circuit len list le  68fc5a2a8b09: P2 M Size Circuit len list le  68fc5a2a8b09
-- statement:
--   The word of a list whose elements have words of length at most B has length at most (number of
--   elements)·(B + 2) + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L69-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L69-L75

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

theorem P2M_SizeCircuit_len_list_le__68fc5a2a8b09 {α : Type} [Enc α] {B : ℕ} : ∀ l : List α, (∀ a ∈ l, len a ≤ B) → len l ≤ l.length * (B + 2) + 2
  := by sorry

alias «SizeCircuit».«len_list_le'» := P2M_SizeCircuit_len_list_le__68fc5a2a8b09
