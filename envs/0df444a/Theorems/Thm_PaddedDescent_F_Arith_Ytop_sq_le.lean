-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Ytop_sq_le
-- name    : PaddedDescent.F.Arith.Ytop_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:45:20.623785+00:00
-- url     : https://prove2.me/theorems/39ba0387-5c44-4da1-bcf3-e8ebefcb4b6b
-- title:
--   Arith: Ytop sq le
-- statement:
--   Y² ≤ n follows from Y⁶ ≤ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L66-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L66-L67

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

theorem PaddedDescent.F.Arith.Ytop_sq_le {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) : Ytop s ^ 2 ≤ n := by sorry
