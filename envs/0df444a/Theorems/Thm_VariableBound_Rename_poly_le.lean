-- Prove2me | Theorems.Thm_VariableBound_Rename_poly_le
-- name    : VariableBound.Rename.poly_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:47.729526+00:00
-- url     : https://prove2.me/theorems/2ac5207a-7ab4-40c0-91a1-227e016bd7a1
-- title:
--   Rename: poly le
-- statement:
--   q·2^q·(a + 1)^q ≤ C·a^C for C = q·4^q and a ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Time.lean#L47-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Time.lean#L47-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_VariableBound_Paper_Rename_Time
set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename

theorem VariableBound.Rename.poly_le (q : ℕ) {a : ℕ} (ha : 1 ≤ a) : q * 2 ^ q * (a + 1) ^ q ≤ q * 4 ^ q * a ^ (q * 4 ^ q) := by sorry
