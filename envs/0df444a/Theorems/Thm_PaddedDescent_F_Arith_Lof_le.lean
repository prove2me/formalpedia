-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Lof_le
-- name    : PaddedDescent.F.Arith.Lof_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:04.719352+00:00
-- url     : https://prove2.me/theorems/4922bf2b-a7fe-48c4-876e-766d0349722b
-- title:
--   Arith: Lof le
-- statement:
--   L ≤ 2·Y·(⌊√n⌋+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L223-L231
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L223-L231

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

theorem PaddedDescent.F.Arith.Lof_le (s n : ℕ) : Lof s n ≤ 2 * Ytop s * (Nat.sqrt n + 1) := by sorry
