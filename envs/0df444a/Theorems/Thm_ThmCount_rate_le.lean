-- Prove2me | Theorems.Thm_ThmCount_rate_le
-- name    : ThmCount.rate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:41:25.024967+00:00
-- url     : https://prove2.me/theorems/39ea8a0b-fdc7-4910-b886-062118e7a40d
-- title:
--   Thm Count: rate le
-- statement:
--   For n ≥ 2 and e ≤ 1/4: n·r(n) ≤ 8·n/(log n)^e, and n/(log n)^e ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L41-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L41-L68

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

theorem ThmCount.rate_le {n : ℕ} (hn : 2 ≤ n) {e : ℝ} (he : e ≤ 1 / 4) :
    (n : ℝ) * SatK.rN 1 (1 / 2) n ≤ 8 * ((n : ℝ) / Real.logb 2 n ^ e) ∧ 1 ≤ (n : ℝ) / Real.logb 2 n ^ e := by sorry
