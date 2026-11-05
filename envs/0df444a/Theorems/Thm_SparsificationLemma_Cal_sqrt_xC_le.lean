-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_sqrt_xC_le
-- name    : SparsificationLemma.Cal.sqrt_xC_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:11:09.809477+00:00
-- url     : https://prove2.me/theorems/c9bc69de-a067-4953-9f0f-9f8b9afbf743
-- title:
--   Cal: sqrt x C le
-- statement:
--   2·x^(3/2) ≤ 363·k³·ε^(−3/2), written with x·√x and ε·√ε. It holds because √32 ≤ 5.66 and
--   2·32·5.66 ≤ 363.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Alpha.lean#L134-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Alpha.lean#L134-L157

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

theorem SparsificationLemma.Cal.sqrt_xC_le {k : ℕ} {ε : ℚ} (hk : 3 ≤ k) (h0 : 0 < ε) :
    2 * ((xC k ε : ℚ) : ℝ) * Real.sqrt ((xC k ε : ℚ) : ℝ) ≤ 363 * (k : ℝ) ^ 3 / ((ε : ℝ) * Real.sqrt (ε : ℝ)) := by sorry
