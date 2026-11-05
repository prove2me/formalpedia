-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_inv_at_top
-- name    : PaddedDescent.F.Arith.inv_at_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:27.668195+00:00
-- url     : https://prove2.me/theorems/12aff338-be82-489b-96e0-74dd659da42f
-- title:
--   Arith: inv at top
-- statement:
--   The invariant holds at the top level, for the instance that the rebalancing makes of a network
--   of marks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L306-L333
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L306-L333

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

theorem PaddedDescent.F.Arith.inv_at_top {k Δ s n : ℕ} (hk : k ≤ s) (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) :
    Inv (depthOf s) (Xof s n) (Zof s) (Qmof k s n) (Wmof k s n) (Lof s n) (depthOf s)
      (lamG (Kseq (depthOf s)) (3 * Kseq (depthOf s) ^ 8) (Ubof k s n) (Pbof Δ s n))
      (Pbof Δ s n * (2 * (3 * Kseq (depthOf s) ^ 8) / Kseq (depthOf s))) 1 := by sorry
