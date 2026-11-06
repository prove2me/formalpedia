-- Prove2me | Theorems.Thm_SizeCircuit_foldl_eq_iterate
-- name    : SizeCircuit.foldl_eq_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:37:31.464574+00:00
-- url     : https://prove2.me/theorems/2dc36c77-1ac2-467f-993e-6593842d88b1
-- title:
--   Size Circuit: foldl eq iterate
-- statement:
--   A fold along a list of strokes that applies f at each stroke applies f as often as the list is
--   long.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L134-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L134-L136

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

theorem SizeCircuit.foldl_eq_iterate {γ : Type} (f : γ → γ) : ∀ (l : List Unit) (a : γ), l.foldl (fun c _ => f c) a = f^[l.length] a
  := by sorry
