-- Prove2me | Theorems.Thm_SizeCircuit_ext_of_lt
-- name    : SizeCircuit.ext_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:37:41.888102+00:00
-- url     : https://prove2.me/theorems/df615784-2453-4c88-8ea3-0ceb9e6a9841
-- title:
--   Size Circuit: ext of lt
-- statement:
--   Below N, the assignment b on N variables, read on all numbers, has the value of b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L152-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L152-L152

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

theorem SizeCircuit.ext_of_lt {N : ℕ} (b : Fin N → Bool) {i : ℕ} (h : i < N) : ext b i = b ⟨i, h⟩ := by sorry
