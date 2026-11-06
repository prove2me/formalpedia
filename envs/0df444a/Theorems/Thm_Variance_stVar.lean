-- Prove2me | Theorems.Thm_Variance_stVar
-- name    : Variance.stVar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:34:54.803496+00:00
-- url     : https://prove2.me/theorems/f54063a6-856c-40a0-8863-b8b21d9920d0
-- title:
--   Variance: st Var
-- statement:
--   «Hence Var Y_{γ,γ'} ≤ Σ_{(a,b)∈[g]²: a≠b} c_{a,b}·4P = 4PU».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Var.lean#L139-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Var.lean#L139-L139

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Cov
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Var
set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks

theorem Variance.stVar : StVar := by sorry
