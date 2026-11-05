-- Prove2me | Theorems.Thm_Variance_stSearchOfGrouping
-- name    : Variance.stSearchOfGrouping
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:35:52.29689+00:00
-- url     : https://prove2.me/theorems/a8f7b608-5e9f-45e6-8397-a85d8bb793dc
-- title:
--   Variance: st Search Of Grouping
-- statement:
--   **«Go through all K^g groupings (a constant) and fix the first good one.»** For g = 3K⁸ there is
--   a first number x < K^g to which the test says yes, and the grouping number x is good as printed;
--   from «a good grouping exists».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L167-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L167-L178

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

theorem Variance.stSearchOfGrouping : StSearchOfGrouping := by sorry
