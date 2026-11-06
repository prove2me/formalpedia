-- Prove2me | Theorems.Thm_ThmCount_natCast_le_two_rpow
-- name    : ThmCount.natCast_le_two_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:10:16.895823+00:00
-- url     : https://prove2.me/theorems/186d34dc-5479-4c98-afb0-e126941e6bdc
-- title:
--   Thm Count: nat Cast le two rpow
-- statement:
--   A natural number q is at most 2^q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L71-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L71-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Tactic
import Definitions.Def_ThmCount_Rates
import Theorems.Thm_VariableBound_Paper_natCast_le_two_rpow

set_option autoImplicit false
section
section
open ThmCount

theorem ThmCount.natCast_le_two_rpow (q : ℕ) : (q : ℝ) ≤ (2 : ℝ) ^ (q : ℝ) := by sorry
