-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_le_ceilMul
-- name    : QueryMachines.Bridge.Proof.le_ceilMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:58:30.059744+00:00
-- url     : https://prove2.me/theorems/3215c84c-f0c1-4d77-b028-59d095a423a8
-- title:
--   Proof: le ceil Mul
-- statement:
--   ⌈min(a/b, 1)·n⌉ from below, for b > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Need.lean#L55-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Need.lean#L55-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_CountedToPadded_Need
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork PaddedDescent.F Printed CliqueLevels

theorem QueryMachines.Bridge.Proof.le_ceilMul {a b : ℕ} (hb : 0 < b) (n : ℕ) : min ((a : ℝ) / b) 1 * n ≤ ceilMul a b n := by sorry
