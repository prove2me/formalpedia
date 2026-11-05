-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_two_logb_le
-- name    : SparsificationLemma.Cal.two_logb_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:46.32073+00:00
-- url     : https://prove2.me/theorems/f13b8e98-b23c-42aa-b249-9ca5753e4099
-- title:
--   Cal: two logb le
-- statement:
--   2·log₂ x ≤ x for x ≥ 128.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Real.lean#L65-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Real.lean#L65-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Real
set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal

theorem SparsificationLemma.Cal.two_logb_le {x : ℝ} (hx : 128 ≤ x) : 2 * Real.logb 2 x ≤ x := by sorry
