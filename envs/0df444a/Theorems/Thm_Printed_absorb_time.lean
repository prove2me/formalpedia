-- Prove2me | Theorems.Thm_Printed_absorb_time
-- name    : Printed.absorb_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:43:48.858205+00:00
-- url     : https://prove2.me/theorems/42093ee6-172a-4300-964e-46138d1bcda0
-- title:
--   Printed: absorb time
-- statement:
--   A bound a·p·x^a on the time may be raised to Cc·p·x^Cc, for a ≤ Cc and x ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Absorb.lean#L38-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Absorb.lean#L38-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_Printed_Absorb
set_option autoImplicit false
section
section
open Printed

theorem Printed.absorb_time {a Cc : ℕ} (h : a ≤ Cc) {p x : ℝ} (hp : 0 ≤ p) (hx : 1 ≤ x) : (a : ℝ) * p * x ^ a ≤ Cc * p * x ^ Cc := by sorry
