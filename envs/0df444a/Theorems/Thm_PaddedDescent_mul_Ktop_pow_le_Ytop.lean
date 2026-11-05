-- Prove2me | Theorems.Thm_PaddedDescent_mul_Ktop_pow_le_Ytop
-- name    : PaddedDescent.mul_Ktop_pow_le_Ytop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:23.165814+00:00
-- url     : https://prove2.me/theorems/c2aa58f0-0b7a-47ac-8b51-5b8fc0c68c03
-- title:
--   Padded Descent: mul Ktop pow le Ytop
-- statement:
--   C·K_t^e ≤ Y for e ≤ 15 and C ≤ 2^500.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Seq.lean#L129-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Seq.lean#L129-L135

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
set_option autoImplicit false
section
section
open PaddedDescent

theorem PaddedDescent.mul_Ktop_pow_le_Ytop {C e : ℕ} (hC : C ≤ 2 ^ 500) (he : e ≤ 15) (s : ℕ) : C * Ktop s ^ e ≤ Ytop s := by sorry
