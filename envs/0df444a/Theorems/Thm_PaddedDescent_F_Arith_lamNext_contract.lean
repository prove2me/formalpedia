-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_lamNext_contract
-- name    : PaddedDescent.F.Arith.lamNext_contract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:48.712204+00:00
-- url     : https://prove2.me/theorems/aeacc134-cdc7-40b4-9f6e-e6e820062877
-- title:
--   Arith: lam Next contract
-- statement:
--   The contraction of one level. With Q = g⁴Λ (the square of the number of nodes times the label
--   length) before the level and
--   Q' = K²·lamNext after it: Q' ≤ (8963/10000)·Q + g⁴.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L55-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L55-L71

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

theorem PaddedDescent.F.Arith.lamNext_contract {K g : ℕ} (hg : K ≤ g) (hg20 : 2 ^ 20 ≤ g) (lam : ℕ) :
    10000 * (K ^ 2 * lamNext K g lam) ≤ 8963 * (g ^ 4 * lam) + 10000 * g ^ 4 := by sorry
