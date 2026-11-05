-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_inv_top_aux
-- name    : PaddedDescent.F.Arith.inv_top_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:06.798713+00:00
-- url     : https://prove2.me/theorems/a7d5c0e8-e726-4ebd-ac8f-de4b5aecb441
-- title:
--   Arith: inv top aux
-- statement:
--   The arithmetic of `inv_top` with plain variables (A = 8963^t, B = 10000^t, q = K²·lamG, v =
--   u·2^s·X).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L65-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L65-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithTop
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {K g Ub P X : ℕ}

theorem PaddedDescent.F.Arith.inv_top_aux {A B q Z v X : ℕ} (h3 : A * (2 * v) ≤ B * X) (h4 : A * X ≤ B * X) (h5 : 4 * q ≤ 4 * Z + 4 * v + X) :
    A * q ≤ B * X + A * Z := by sorry
