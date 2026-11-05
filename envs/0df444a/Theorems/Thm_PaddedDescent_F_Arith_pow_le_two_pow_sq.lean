-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_pow_le_two_pow_sq
-- name    : PaddedDescent.F.Arith.pow_le_two_pow_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:44:18.156956+00:00
-- url     : https://prove2.me/theorems/cfee0563-bdc3-46f8-a0b4-543c5f35ad55
-- title:
--   Arith: pow le two pow sq
-- statement:
--   The colourings: K^g ≤ 2^{g·g}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L132-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L132-L133

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

theorem PaddedDescent.F.Arith.pow_le_two_pow_sq {K g : ℕ} (hg : K ≤ g) : K ^ g ≤ 2 ^ (g * g) := by sorry
