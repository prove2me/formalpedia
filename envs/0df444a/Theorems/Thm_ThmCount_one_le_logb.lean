-- Prove2me | Theorems.Thm_ThmCount_one_le_logb
-- name    : ThmCount.one_le_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:23:29.403255+00:00
-- url     : https://prove2.me/theorems/dad85ae8-36b1-4215-a876-90ee528e11e3
-- title:
--   Thm Count: one le logb
-- statement:
--   log₂ n ≥ 1 for n ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L36-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L36-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Tactic
import Definitions.Def_ThmCount_Rates
import Theorems.Thm_Sat3_one_le_logb

set_option autoImplicit false
section
section
open ThmCount

theorem ThmCount.one_le_logb {x : ℝ} (hx : 2 ≤ x) : 1 ≤ Real.logb 2 x := by sorry
