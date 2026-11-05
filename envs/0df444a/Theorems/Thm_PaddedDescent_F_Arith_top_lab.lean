-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_top_lab
-- name    : PaddedDescent.F.Arith.top_lab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:36.594657+00:00
-- url     : https://prove2.me/theorems/12c99086-be56-4f49-874f-38f018047e1f
-- title:
--   Arith: top lab
-- statement:
--   Field lab of NetFits: the labels inside a class at the top.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L361-L363
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L361-L363

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

theorem PaddedDescent.F.Arith.top_lab (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) (hF : 2 ^ (8 * Xof s n) ≤ F) : 2 ^ Pbof Δ s n ≤ F := by sorry
