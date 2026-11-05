-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Qmof_lt
-- name    : PaddedDescent.F.Arith.Qmof_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:45:35.139883+00:00
-- url     : https://prove2.me/theorems/33e78e73-f6b7-4e62-8486-0980eac26bf8
-- title:
--   Arith: Qmof lt
-- statement:
--   Qm + 1 ≤ 2^L.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L178-L193
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L178-L193

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

theorem PaddedDescent.F.Arith.Qmof_lt {k s n : ℕ} (hk : k ≤ s) (hY : Ytop s ^ 6 ≤ n) : Qmof k s n + 1 ≤ 2 ^ Lof s n := by sorry
