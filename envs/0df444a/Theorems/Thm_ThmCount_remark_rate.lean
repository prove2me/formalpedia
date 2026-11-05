-- Prove2me | Theorems.Thm_ThmCount_remark_rate
-- name    : ThmCount.remark_rate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:10:20.930798+00:00
-- url     : https://prove2.me/theorems/2679c2bc-be32-4477-b8c6-0e5a4bcc5875
-- title:
--   Thm Count: remark rate
-- statement:
--   For n ≥ 4, R = n·(log log n)^{2/3}/(log n)^{1/6} has n·r(n) ≤ 8·R and R ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L154-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L154-L173

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Tactic
import Definitions.Def_ThmCount_Rates
set_option autoImplicit false
section
section
open ThmCount

theorem ThmCount.remark_rate {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) * SatK.rN 1 (1 / 2) n ≤ 8 * ((n : ℝ) * Real.logb 2 (Real.logb 2 n) ^ ((2 : ℝ) / 3) / Real.logb 2 n ^ ((1 : ℝ) / 6)) ∧
      1 ≤ (n : ℝ) * Real.logb 2 (Real.logb 2 n) ^ ((2 : ℝ) / 3) / Real.logb 2 n ^ ((1 : ℝ) / 6) := by sorry
