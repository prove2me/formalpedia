-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_mul_Pn_eq
-- name    : PaddedDescent.F.Arith.mul_Pn_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:54.191167+00:00
-- url     : https://prove2.me/theorems/d044af1a-c331-40f0-aaa1-e512aa8e56ba
-- title:
--   Arith: mul Pn eq
-- statement:
--   The labels inside a class: g times the exponent is 2g⁴Λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L115-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L115-L116

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithLevel
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F

theorem PaddedDescent.F.Arith.mul_Pn_eq (g lam : ℕ) : g * Pn g lam = 2 * (g ^ 4 * lam) := by sorry
