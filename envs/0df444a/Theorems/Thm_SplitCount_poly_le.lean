-- Prove2me | Theorems.Thm_SplitCount_poly_le
-- name    : SplitCount.poly_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:39:20.886867+00:00
-- url     : https://prove2.me/theorems/efa4a85e-4569-438d-a596-5168ecb7f8a5
-- title:
--   Split Count: poly le
-- statement:
--   For s ≥ 1: if x ≤ B·s^d + A·(P·s^e)^A then x ≤ c·s^c with c = B + d + A·P^A + e·A.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L104-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitCount/Sizes.lean#L104-L114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes
set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat

theorem SplitCount.poly_le {s A B P d e x : ℕ} (hs : 1 ≤ s) (hx : x ≤ B * s ^ d + A * (P * s ^ e) ^ A) :
    x ≤ (B + d + A * P ^ A + e * A) * s ^ (B + d + A * P ^ A + e * A) := by sorry
