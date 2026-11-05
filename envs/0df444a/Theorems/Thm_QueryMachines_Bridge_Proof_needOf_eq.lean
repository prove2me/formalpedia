-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_needOf_eq
-- name    : QueryMachines.Bridge.Proof.needOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:17:52.933955+00:00
-- url     : https://prove2.me/theorems/7be80874-ed50-4c7f-a431-6739936eb230
-- title:
--   Proof: need Of eq
-- statement:
--   The exponent at the index (ℓ, k), written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Need.lean#L103-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Need.lean#L103-L105

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

theorem QueryMachines.Bridge.Proof.needOf_eq (num : U × U → ℕ × ℕ) (C₀ l k lam B : ℕ) : needOf num C₀ ((unary l, unary k), unary lam, unary B) =
    ceilMul (num (unary l, unary k)).1 (num (unary l, unary k)).2 (k ^ 2 * lam) + C₀ * k ^ 2 * Nat.size (k * (lam + B + 1)) + 2 := by sorry
