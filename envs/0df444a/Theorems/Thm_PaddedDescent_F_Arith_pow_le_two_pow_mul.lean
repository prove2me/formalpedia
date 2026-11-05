-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_pow_le_two_pow_mul
-- name    : PaddedDescent.F.Arith.pow_le_two_pow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:22.981439+00:00
-- url     : https://prove2.me/theorems/3e8f9159-30b4-47f5-a13d-6677ae3e246f
-- title:
--   Arith: pow le two pow mul
-- statement:
--   The colourings: K^g ≤ 2^{Kg}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L127-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L127-L129

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

theorem PaddedDescent.F.Arith.pow_le_two_pow_mul (K g : ℕ) : K ^ g ≤ 2 ^ (K * g) := by sorry
