-- Prove2me | Theorems.Thm_Variance_stSearch
-- name    : Variance.stSearch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:21:28.638756+00:00
-- url     : https://prove2.me/theorems/f06b52be-fa7f-4a62-ae95-5d19b31066cf
-- title:
--   Variance: st Search
-- statement:
--   «Go through all K^g groupings (a constant) and fix the first good one», on the variance summed
--   from the covariances. (Not the theorem of the same name in `Eight.ViaGrouping`.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L182-L182
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L182-L182

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
import Theorems.Thm_Eight_ViaGrouping_stSearch
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks Eight.ViaGrouping

theorem Variance.stSearch : Eight.ViaGrouping.StSearch := by sorry
