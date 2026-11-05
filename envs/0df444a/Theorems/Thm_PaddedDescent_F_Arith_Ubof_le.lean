-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Ubof_le
-- name    : PaddedDescent.F.Arith.Ubof_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:47:54.327927+00:00
-- url     : https://prove2.me/theorems/4b524a3e-fb27-4b96-88bc-010531b11130
-- title:
--   Arith: Ubof le
-- statement:
--   Ub ≤ 4·(s + 8)⁶·n + 8·(s + 8)²·Y, for every width k ≤ s.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L99-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L99-L129

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F

theorem PaddedDescent.F.Arith.Ubof_le {k s : ℕ} (hk : k ≤ s) (n : ℕ) : Ubof k s n ≤ 4 * (s + 8) ^ 6 * n + 8 * (s + 8) ^ 2 * Ytop s := by sorry
