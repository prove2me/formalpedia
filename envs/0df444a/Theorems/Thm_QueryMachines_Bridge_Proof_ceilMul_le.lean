-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_ceilMul_le
-- name    : QueryMachines.Bridge.Proof.ceilMul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:58:33.221334+00:00
-- url     : https://prove2.me/theorems/5b1d4953-aaf8-46b4-abb8-725567220523
-- title:
--   Proof: ceil Mul le
-- statement:
--   ⌈min(a/b, 1)·n⌉ from above, for b > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Need.lean#L72-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Need.lean#L72-L87

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

theorem QueryMachines.Bridge.Proof.ceilMul_le {a b : ℕ} (hb : 0 < b) (n : ℕ) : (ceilMul a b n : ℝ) ≤ min ((a : ℝ) / b) 1 * n + 1 := by sorry
