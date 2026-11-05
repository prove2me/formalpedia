-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_alphaC_le_sqrt
-- name    : SparsificationLemma.Cal.alphaC_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:11:20.662227+00:00
-- url     : https://prove2.me/theorems/3e7c8db0-a487-4f5c-a5c7-eeb4c0004c1e
-- title:
--   Cal: alpha C le sqrt
-- statement:
--   32α ≤ 2x·⌈log₂ x⌉ + 32 ≤ 2·x^(3/2), written 2·x·√x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Alpha.lean#L120-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Alpha.lean#L120-L130

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

theorem SparsificationLemma.Cal.alphaC_le_sqrt {k : ℕ} {ε : ℚ} (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    32 * (alphaC k ε : ℝ) ≤ 2 * ((xC k ε : ℚ) : ℝ) * Real.sqrt ((xC k ε : ℚ) : ℝ) := by sorry
