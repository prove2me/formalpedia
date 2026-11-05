-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_xC_cast
-- name    : SparsificationLemma.Cal.xC_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:24:28.219701+00:00
-- url     : https://prove2.me/theorems/8a6ff133-a68f-483c-9bd3-4e657895293c
-- title:
--   Cal: x C cast
-- statement:
--   x as a real number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Alpha.lean#L116-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Alpha.lean#L116-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Alpha
set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal

theorem SparsificationLemma.Cal.xC_cast (k : ℕ) (ε : ℚ) : ((xC k ε : ℚ) : ℝ) = 32 * ((k : ℝ) - 1) ^ 2 / (ε : ℝ) := by sorry
