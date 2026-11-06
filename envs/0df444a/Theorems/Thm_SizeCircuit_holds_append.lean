-- Prove2me | Theorems.Thm_SizeCircuit_holds_append
-- name    : SizeCircuit.holds_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:37:36.069683+00:00
-- url     : https://prove2.me/theorems/847b83eb-fb8b-4590-92a5-5662cc771052
-- title:
--   Size Circuit: holds append
-- statement:
--   Two formulas written one after the other hold exactly if both hold.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L42-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/General.lean#L42-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_CircuitLowerBound_Circ_Form
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_General
import Theorems.Thm_CountKSat_StepCount_holds_append

set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat CircuitLowerBound CircuitLowerBound.Blocks ENP

theorem SizeCircuit.holds_append (a : ℕ → Bool) (φ ψ : Fml) : Holds a (φ ++ ψ) ↔ Holds a φ ∧ Holds a ψ := by sorry
