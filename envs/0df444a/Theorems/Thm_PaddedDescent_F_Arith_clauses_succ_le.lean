-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_clauses_succ_le
-- name    : PaddedDescent.F.Arith.clauses_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:38.001997+00:00
-- url     : https://prove2.me/theorems/2f86a42b-bb5c-4508-8353-8d36eb5659be
-- title:
--   Arith: clauses succ le
-- statement:
--   The number of clauses of a sparsified formula, plus one, is at most 2^(β + size n).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithMark.lean#L29-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithMark.lean#L29-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithMark
set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent

theorem PaddedDescent.F.Arith.clauses_succ_le {Δ s : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (n : ℕ) : Δ * n + 1 ≤ 2 ^ (betaOf s + Nat.size n) := by sorry
