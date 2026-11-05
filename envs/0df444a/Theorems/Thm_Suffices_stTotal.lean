-- Prove2me | Theorems.Thm_Suffices_stTotal
-- name    : Suffices.stTotal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:29:59.125995+00:00
-- url     : https://prove2.me/theorems/821882bf-a44c-48d1-80c2-d96311068309
-- title:
--   Suffices: st Total
-- statement:
--   **«Lemma 4 yields at most 2^{δn/3} such formulas, in time 2^{δn/3} times a polynomial in n, … so
--   the total time is O(2^{δn})»** (proof of Theorem 2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Total.lean#L29-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Total.lean#L29-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Defs
import Definitions.Def_StepMachines_Math_SatArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Suffices_Total
set_option autoImplicit false
section
section
open Suffices

theorem Suffices.stTotal : StTotal := by sorry
