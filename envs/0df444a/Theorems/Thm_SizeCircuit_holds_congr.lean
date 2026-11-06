-- Prove2me | Theorems.Thm_SizeCircuit_holds_congr
-- name    : SizeCircuit.holds_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:37:58.183856+00:00
-- url     : https://prove2.me/theorems/972d78fa-1aa4-4dca-ab70-1b5fe43cd4f5
-- title:
--   Size Circuit: holds congr
-- statement:
--   Whether a formula holds depends only on the values of the variables that occur in it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L46-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L46-L53

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

theorem SizeCircuit.holds_congr {a a' : ℕ → Bool} {ψ : Fml} (h : ∀ C ∈ ψ, ∀ l ∈ C, a l.1 = a' l.1) : Holds a ψ ↔ Holds a' ψ := by sorry
