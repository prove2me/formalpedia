-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_logb_le_sqrt_sub
-- name    : SparsificationLemma.Cal.logb_le_sqrt_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:23:04.117784+00:00
-- url     : https://prove2.me/theorems/a719141f-f81a-4dfa-8c00-ccf870a98459
-- title:
--   Cal: logb le sqrt sub
-- statement:
--   log₂ x ≤ √x − 9/8 for x ≥ 128.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Real.lean#L33-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Real.lean#L33-L46

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

theorem SparsificationLemma.Cal.logb_le_sqrt_sub {x : ℝ} (hx : 128 ≤ x) : Real.logb 2 x ≤ Real.sqrt x - 9 / 8 := by sorry
