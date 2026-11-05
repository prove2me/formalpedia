-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_hundred_Ytop_le
-- name    : PaddedDescent.F.Arith.hundred_Ytop_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:45:29.756206+00:00
-- url     : https://prove2.me/theorems/75e0d77b-02d1-4fc1-af7f-bae38d9ee5ad
-- title:
--   Arith: hundred Ytop le
-- statement:
--   100·Y ≤ n follows from Y⁶ ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L70-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L70-L74

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

theorem PaddedDescent.F.Arith.hundred_Ytop_le {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) : 100 * Ytop s ≤ n := by sorry
