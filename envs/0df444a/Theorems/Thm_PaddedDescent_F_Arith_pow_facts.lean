-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_pow_facts
-- name    : PaddedDescent.F.Arith.pow_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:36.336115+00:00
-- url     : https://prove2.me/theorems/ae60470e-7d4a-4e59-b1ce-d6d60bb96439
-- title:
--   Arith: pow facts
-- statement:
--   24K³ ≤ 16(g·g)³ and 2K² ≤ (g·g)², if 2K ≤ g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L155-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L155-L162

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithLevel
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F

theorem PaddedDescent.F.Arith.pow_facts {K g : ℕ} (hg : 2 * K ≤ g) :
    24 * K ^ 3 ≤ 16 * (g * g) ^ 3 ∧ 2 * K ^ 2 ≤ (g * g) ^ 2 := by sorry
