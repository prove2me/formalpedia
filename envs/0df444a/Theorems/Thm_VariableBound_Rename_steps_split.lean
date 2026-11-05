-- Prove2me | Theorems.Thm_VariableBound_Rename_steps_split
-- name    : VariableBound.Rename.steps_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:46.002999+00:00
-- url     : https://prove2.me/theorems/fbaa3216-cb26-4200-b792-3bcf18b4b33f
-- title:
--   Rename: steps split
-- statement:
--   q·(a + 2^E + 1)^q ≤ q·2^q·(a + 1)^q + 2q·(b + 2^E + 1)^(2q), for all natural numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Time.lean#L25-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Time.lean#L25-L40

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

theorem VariableBound.Rename.steps_split (q a b E : ℕ) : q * (a + 2 ^ E + 1) ^ q ≤ q * 2 ^ q * (a + 1) ^ q + 2 * q * (b + 2 ^ E + 1) ^ (2 * q) := by sorry
