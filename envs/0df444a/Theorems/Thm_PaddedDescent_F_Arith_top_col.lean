-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_top_col
-- name    : PaddedDescent.F.Arith.top_col
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:30.108557+00:00
-- url     : https://prove2.me/theorems/15c97e3c-e3ac-4652-bdc2-6391e8d4c6a2
-- title:
--   Arith: top col
-- statement:
--   Field col of NetFits: the colourings at the top.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L346-L352
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L346-L352

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

theorem PaddedDescent.F.Arith.top_col (hY : Ytop s ^ 6 ≤ n) (hF : 2 ^ (8 * Xof s n) ≤ F) :
    Kseq (depthOf s) ^ (3 * Kseq (depthOf s) ^ 8) ≤ F := by sorry
