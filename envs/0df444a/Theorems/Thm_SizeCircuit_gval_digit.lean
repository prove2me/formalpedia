-- Prove2me | Theorems.Thm_SizeCircuit_gval_digit
-- name    : SizeCircuit.gval_digit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:41:45.028213+00:00
-- url     : https://prove2.me/theorems/a0c77dbf-618d-4e35-8b02-911393a69b17
-- title:
--   Size Circuit: gval digit
-- statement:
--   The gate "the wire i, and the wire j has the value t".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L51-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L51-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Compare
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.gval_digit (v : ℕ → Bool) (t : Bool) (i j : ℕ) : gval v ((if t then opAnd else opAndN), i, j) = (v i && (v j == t)) := by sorry
