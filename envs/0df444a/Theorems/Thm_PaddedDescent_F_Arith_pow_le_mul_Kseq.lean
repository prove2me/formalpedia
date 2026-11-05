-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_pow_le_mul_Kseq
-- name    : PaddedDescent.F.Arith.pow_le_mul_Kseq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:13.299689+00:00
-- url     : https://prove2.me/theorems/582fc1ed-7bed-4082-bdc5-a162dbe0c984
-- title:
--   Arith: pow le mul Kseq
-- statement:
--   10000^j ≤ 8963^j·K_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L60-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L60-L64

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

theorem PaddedDescent.F.Arith.pow_le_mul_Kseq (j : ℕ) : 10000 ^ j ≤ 8963 ^ j * Kseq j := by sorry
