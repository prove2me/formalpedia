-- Prove2me | Theorems.Thm_Variance_stTotalLe
-- name    : Variance.stTotalLe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:35:35.301132+00:00
-- url     : https://prove2.me/theorems/40430538-08bc-461e-a39c-b802734ac48e
-- title:
--   Variance: st Total Le
-- statement:
--   «4PU ≤ 4gP²»: U ≤ gP, by (i) of Definition 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L53-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L53-L53

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

theorem Variance.stTotalLe : StTotalLe := by sorry
