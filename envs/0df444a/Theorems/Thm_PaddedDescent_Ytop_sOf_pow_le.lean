-- Prove2me | Theorems.Thm_PaddedDescent_Ytop_sOf_pow_le
-- name    : PaddedDescent.Ytop_sOf_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:40:05.236966+00:00
-- url     : https://prove2.me/theorems/e3fbd8a6-ef47-4b4c-a972-1d4508f48a66
-- title:
--   Padded Descent: Ytop s Of pow le
-- statement:
--   If sOf n ≥ 1 then Y^p ≤ n for Y = Ytop (sOf n) and every p ≤ 2^200.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L104-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L104-L105

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_Threshold
set_option autoImplicit false
section
section
open PaddedDescent

theorem PaddedDescent.Ytop_sOf_pow_le {n p : ℕ} (hp : p ≤ 2 ^ 200) (h : 1 ≤ sOf n) : Ytop (sOf n) ^ p ≤ n := by sorry
