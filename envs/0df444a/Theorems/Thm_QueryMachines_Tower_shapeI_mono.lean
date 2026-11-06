-- Prove2me | Theorems.Thm_QueryMachines_Tower_shapeI_mono
-- name    : QueryMachines.Tower.shapeI_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:46:02.314624+00:00
-- url     : https://prove2.me/theorems/cc8c4f64-5b7d-480c-841c-0445784f8549
-- title:
--   Tower: shape I mono
-- statement:
--   The shape of the procedure's cost is monotone in the price.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Cost.lean#L33-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Tower/Cost.lean#L33-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Defs
import Mathlib.Tactic.Ring
import Definitions.Def_Tower_Cost
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower

theorem QueryMachines.Tower.shapeI_mono (own' q' : ℕ → ℕ) (l t t' : ℕ) (h : t ≤ t') : shapeI own' q' l t ≤ shapeI own' q' l t' := by sorry
