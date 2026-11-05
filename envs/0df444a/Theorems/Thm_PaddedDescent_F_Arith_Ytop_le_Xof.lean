-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Ytop_le_Xof
-- name    : PaddedDescent.F.Arith.Ytop_le_Xof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:45:51.03551+00:00
-- url     : https://prove2.me/theorems/0f66cc58-9770-4555-b696-272e8682a282
-- title:
--   Arith: Ytop le Xof
-- statement:
--   65·Y ≤ X.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L263-L269
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L263-L269

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

theorem PaddedDescent.F.Arith.Ytop_le_Xof {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) : 65 * Ytop s ≤ Xof s n := by sorry
