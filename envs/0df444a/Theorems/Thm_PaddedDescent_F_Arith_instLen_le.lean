-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_instLen_le
-- name    : PaddedDescent.F.Arith.instLen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:23.445638+00:00
-- url     : https://prove2.me/theorems/93662ef8-2d21-4643-85e0-921d9458e8b0
-- title:
--   Arith: inst Len le
-- statement:
--   The length of an instance: the number of table entries of a row times a polynomial factor.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L136-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithLevel.lean#L136-L141

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

theorem PaddedDescent.F.Arith.instLen_le (K lam B : ℕ) : instLen K lam B ≤ 2 ^ ((K - 1) * lam) * (K * (3 * B + 14) + 4 * lam + 10) := by sorry
