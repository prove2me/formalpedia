-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_div_sqrt_le_cube
-- name    : SparsificationLemma.Cal.div_sqrt_le_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:11:32.605207+00:00
-- url     : https://prove2.me/theorems/297d25f6-0d3f-4dd4-b759-b0880eeb6a0a
-- title:
--   Cal: div sqrt le cube
-- statement:
--   363·k³·ε^(−3/2) ≤ (8k/ε)³ for ε ∈ (0,1], because ε³ ≤ ε·√ε and 363 ≤ 512.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Alpha.lean#L160-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Alpha.lean#L160-L171

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

theorem SparsificationLemma.Cal.div_sqrt_le_cube (k : ℕ) {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    363 * (k : ℝ) ^ 3 / ((ε : ℝ) * Real.sqrt (ε : ℝ)) ≤ (8 * (k : ℝ) / (ε : ℝ)) ^ 3 := by sorry
