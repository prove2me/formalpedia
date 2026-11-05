-- Prove2me | Theorems.Thm_Variance_stSomePairOfCheb
-- name    : Variance.stSomePairOfCheb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:35:47.662235+00:00
-- url     : https://prove2.me/theorems/49a95806-da23-4e45-9785-11c563169895
-- title:
--   Variance: st Some Pair Of Cheb
-- statement:
--   «By a union bound over the fewer than K²/2 pairs of groups, some pair violates this bound with
--   probability less than» (K²/2)·(4K⁶/g): the union runs over the pairs γ < γ' only, since Y_{γ,γ'} =
--   Y_{γ',γ}. The proof is that of `Eight.SecNetworks.some_pair`, from the hypothesis.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L94-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L94-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Var
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_Eight_SecNetworks_Grouping
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Grouping
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks Eight.ViaGrouping

theorem Variance.stSomePairOfCheb : StSomePairOfCheb := by sorry
