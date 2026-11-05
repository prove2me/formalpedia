-- Prove2me | Theorems.Thm_SparsificationLemma_Cal_clog_eq_ceil_logb
-- name    : SparsificationLemma.Cal.clog_eq_ceil_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:50.56884+00:00
-- url     : https://prove2.me/theorems/b614c06c-c67b-4e73-9a48-b345240b5e28
-- title:
--   Cal: clog eq ceil logb
-- statement:
--   For a rational x ≥ 1: `Nat.clog 2 ⌈x⌉₊` = ⌈log₂ x⌉.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Alpha.lean#L58-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Cal/Alpha.lean#L58-L65

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

theorem SparsificationLemma.Cal.clog_eq_ceil_logb {x : ℚ} (hx : 1 ≤ x) : ((Nat.clog 2 ⌈x⌉₊ : ℕ) : ℤ) = ⌈Real.logb 2 (x : ℝ)⌉ := by sorry
