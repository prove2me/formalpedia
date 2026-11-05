-- Prove2me | Theorems.Thm_ThmCount_sqrt_sqrt_eq
-- name    : ThmCount.sqrt_sqrt_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:09:55.884006+00:00
-- url     : https://prove2.me/theorems/17dfc965-c91d-4ce4-96a2-ff53f4c593e3
-- title:
--   Thm Count: sqrt sqrt eq
-- statement:
--   The fourth root, written with two square roots.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L31-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/ThmCount/Rates.lean#L31-L33

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

theorem ThmCount.sqrt_sqrt_eq {x : ℝ} (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x ^ ((1 : ℝ) / 4) := by sorry
