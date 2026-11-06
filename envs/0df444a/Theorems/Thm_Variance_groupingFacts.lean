-- Prove2me | Theorems.Thm_Variance_groupingFacts
-- name    : Variance.groupingFacts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T07:59:54.226234+00:00
-- url     : https://prove2.me/theorems/ecd7ef85-c293-447f-92f0-ba16b53a8047
-- title:
--   Variance: grouping Facts
-- statement:
--   «A good grouping exists», with the numbers of the text, on the variance summed from the
--   covariances. (Not the theorem of the same name in `Eight.SecNetworks`.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L162-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L162-L162

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
import Theorems.Thm_Eight_SecNetworks_groupingFacts
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks Eight.ViaGrouping

theorem Variance.groupingFacts : GroupingFacts := by sorry
