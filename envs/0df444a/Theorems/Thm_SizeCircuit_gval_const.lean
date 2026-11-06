-- Prove2me | Theorems.Thm_SizeCircuit_gval_const
-- name    : SizeCircuit.gval_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:36:47.870067+00:00
-- url     : https://prove2.me/theorems/842c4938-7624-49e9-8684-40f76d71b361
-- title:
--   Size Circuit: gval const
-- statement:
--   The gate with a constant value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L45-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L45-L48

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

theorem SizeCircuit.gval_const (v : ℕ → Bool) (c : Prop) [Decidable c] (i j : ℕ) : gval v ((if c then opOne else opZero), i, j) = decide c := by sorry
