-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_four_mul_Dcol_sq_mul
-- name    : PaddedDescent.F.Arith.four_mul_Dcol_sq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:00.887057+00:00
-- url     : https://prove2.me/theorems/0854770d-d915-4fac-b9c8-c4f4d38e29a8
-- title:
--   Arith: four mul Dcol sq mul
-- statement:
--   4·D²·2^(9+j)·K_j = g_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithCol.lean#L28-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithCol.lean#L28-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithCol
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent

theorem PaddedDescent.F.Arith.four_mul_Dcol_sq_mul (j : ℕ) : 4 * Dcol ^ 2 * 2 ^ (9 + j) * Kseq j = gseq j := by sorry
