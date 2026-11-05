-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_inv_top
-- name    : PaddedDescent.F.Arith.inv_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:21.321912+00:00
-- url     : https://prove2.me/theorems/a4386e6f-0c46-4b46-8e05-9599c0ecc22c
-- title:
--   Arith: inv top
-- statement:
--   The bound 8963^t·(K²·lamG) ≤ 10000^t·X + 8963^t·Z for the instance at the top of the descent: if
--   Ub ≤ u·n + r, n ≤ 2^s·X and t levels make up for the factor 2·u·2^s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L72-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTop.lean#L72-L85

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

theorem PaddedDescent.F.Arith.inv_top {t Z u r n s : ℕ} (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) (hU : Ub ≤ u * n + r) (hn : n ≤ 2 ^ s * X)
    (ht : 8963 ^ t * (2 * u * 2 ^ s) ≤ 10000 ^ t) (hZ : K ^ 2 + r ≤ Z) :
    8963 ^ t * (K ^ 2 * lamG K g Ub P) ≤ 10000 ^ t * X + 8963 ^ t * Z := by sorry
