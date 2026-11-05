-- Prove2me | Theorems.Thm_PaddedDescent_Ytop_pow_le
-- name    : PaddedDescent.Ytop_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:32:34.084204+00:00
-- url     : https://prove2.me/theorems/b4e71026-2ebf-4494-b3d8-c5e8feca6d5c
-- title:
--   Padded Descent: Ytop pow le
-- statement:
--   Y^p ≤ 2^(2^(t+211)), t = depthOf s, for every p ≤ 2^200.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L76-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L76-L82

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

theorem PaddedDescent.Ytop_pow_le {p : ℕ} (hp : p ≤ 2 ^ 200) (s : ℕ) : Ytop s ^ p ≤ 2 ^ 2 ^ (depthOf s + 211) := by sorry
