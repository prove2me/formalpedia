-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_pow_succ_le_mul_Kseq
-- name    : PaddedDescent.F.Arith.pow_succ_le_mul_Kseq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:56.445741+00:00
-- url     : https://prove2.me/theorems/654bbfab-7fdc-4055-8c2a-f00332cf236a
-- title:
--   Arith: pow succ le mul Kseq
-- statement:
--   10000^(j+1) ≤ 8963^(j+1)·K_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L53-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L53-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)

theorem PaddedDescent.F.Arith.pow_succ_le_mul_Kseq (j : ℕ) : 10000 ^ (j + 1) ≤ 8963 ^ (j + 1) * Kseq j := by sorry
