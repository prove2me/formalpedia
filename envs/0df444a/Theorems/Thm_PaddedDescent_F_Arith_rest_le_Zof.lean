-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_rest_le_Zof
-- name    : PaddedDescent.F.Arith.rest_le_Zof
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:48:53.113638+00:00
-- url     : https://prove2.me/theorems/5a51a3c5-2e19-4e59-8bd3-0d0e8853440b
-- title:
--   Arith: rest le Zof
-- statement:
--   K_t² + 8·(s + 8)²·Y ≤ Z.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L167-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L167-L175

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

theorem PaddedDescent.F.Arith.rest_le_Zof (s : ℕ) : Ktop s ^ 2 + 8 * (s + 8) ^ 2 * Ytop s ≤ Zof s := by sorry
