-- Prove2me | Theorems.Thm_ThmCount_time_le
-- name    : ThmCount.time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:40:11.384811+00:00
-- url     : https://prove2.me/theorems/4ab792f8-a9e4-4447-a89a-22cfc1fadfdc
-- title:
--   Thm Count: time le
-- statement:
--   For all constants C, q, a, d there is K such that, for every n and every real R ≥ 1 with n·r(n)
--   ≤ 8·R: q·(2^{C·9·(n+4)·log log(n+4)/√(log(n+4))} + a·(n+2)^d + 1)^q ≤ 2^{K·R}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L77-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L77-L142

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

theorem ThmCount.time_le (C q a d : ℕ) : ∃ K : ℝ, ∀ (n : ℕ) (R : ℝ), (n : ℝ) * SatK.rN 1 (1 / 2) n ≤ 8 * R → 1 ≤ R →
    (q : ℝ) * ((2 : ℝ) ^ ((C : ℝ) * MainTheoremForms.expN 3 (n + 4)) + (a : ℝ) * ((n : ℝ) + 2) ^ d + 1) ^ q ≤ (2 : ℝ) ^ (K * R) := by sorry
