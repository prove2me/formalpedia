-- Prove2me | Theorems.Thm_Variance_stVarOf
-- name    : Variance.stVarOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:35:19.431163+00:00
-- url     : https://prove2.me/theorems/a104016c-db38-4dc1-aa44-43455b586f18
-- title:
--   Variance: st Var Of
-- statement:
--   «Hence Var Y_{γ,γ'} ≤ 4PU», put together from the sentences before it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Var.lean#L131-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Var.lean#L131-L136

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

theorem Variance.stVarOf : StVarOf := by sorry
