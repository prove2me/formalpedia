-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_mul_Pn_mul_le
-- name    : PaddedDescent.F.Arith.mul_Pn_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:58.409418+00:00
-- url     : https://prove2.me/theorems/8bc7f961-2904-4a2a-b35a-8c08e4c89277
-- title:
--   Arith: mul Pn mul le
-- statement:
--   The states of a class: K times the exponent is at most 4g⁴Λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L108-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L108-L112

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

theorem PaddedDescent.F.Arith.mul_Pn_mul_le (K g lam : ℕ) : K * (Pn g lam * (2 * g / K)) ≤ 4 * (g ^ 4 * lam) := by sorry
