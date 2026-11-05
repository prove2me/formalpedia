-- Prove2me | Theorems.Thm_ThmCount_stRates
-- name    : ThmCount.stRates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:41:17.517616+00:00
-- url     : https://prove2.me/theorems/b90c4c2e-46f9-4570-af05-8826df782d22
-- title:
--   Thm Count: st Rates
-- statement:
--   The comparison of the rates: for all constants C, q, a, d there is C' such that for every n ≥ 2,
--   q·(2^{C·9·(n+4)·log log(n+4)/√(log(n+4))} + a·(n+2)^d + 1)^q ≤ 2^{C'·n/(log n)^{1/20}}. This is the
--   statement `ThmCount.StRates`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L147-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L147-L151

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

theorem ThmCount.stRates : StRates := by sorry
