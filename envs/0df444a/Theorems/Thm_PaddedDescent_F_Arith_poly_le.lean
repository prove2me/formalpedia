-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_poly_le
-- name    : PaddedDescent.F.Arith.poly_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:45:37.338686+00:00
-- url     : https://prove2.me/theorems/cbb26f6b-e39d-4733-8f01-71f5167d79ae
-- title:
--   Arith: poly le
-- statement:
--   The polynomial factor in the length of an instance is at most 2^(2L).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L200-L218
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L200-L218

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

theorem PaddedDescent.F.Arith.poly_le {k s n : ℕ} (hk : k ≤ s) (hY : Ytop s ^ 6 ≤ n) :
    Kseq (depthOf s) * (3 * Wmof k s n + 14) + 4 * Qmof k s n + 10 ≤ 2 ^ (2 * Lof s n) := by sorry
