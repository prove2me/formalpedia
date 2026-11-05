-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_top_tab
-- name    : PaddedDescent.F.Arith.top_tab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:20.584981+00:00
-- url     : https://prove2.me/theorems/5b48ff30-28ad-410f-9b54-d74e886e2e17
-- title:
--   Arith: top tab
-- statement:
--   Field tab of NetFits: the indices of a table at the top.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L366-L379
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L366-L379

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
variable {k Δ s n F : ℕ}

theorem PaddedDescent.F.Arith.top_tab (hk : k ≤ s) (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) (hF : 2 ^ (8 * Xof s n) ≤ F) :
    2 ^ ((Kseq (depthOf s) - 1) * lamG (Kseq (depthOf s)) (3 * Kseq (depthOf s) ^ 8) (Ubof k s n) (Pbof Δ s n)) ≤ F := by sorry
