-- Prove2me | Theorems.Thm_PaddedDescent_sOf_mul_add_le
-- name    : PaddedDescent.sOf_mul_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:32:36.949196+00:00
-- url     : https://prove2.me/theorems/0e59400d-b0ca-450d-9d3e-e311d150afbe
-- title:
--   Padded Descent: s Of mul add le
-- statement:
--   If sOf n ≥ 1 then depthOf (sOf n) + 211 ≤ ⌊log₂⌊log₂ n⌋⌋.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L92-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L92-L93

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

theorem PaddedDescent.sOf_mul_add_le {n : ℕ} (h : 1 ≤ sOf n) : depthOf (sOf n) + 211 ≤ Nat.log2 (Nat.log2 n) := by sorry
