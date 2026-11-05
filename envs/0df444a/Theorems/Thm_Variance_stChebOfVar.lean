-- Prove2me | Theorems.Thm_Variance_stChebOfVar
-- name    : Variance.stChebOfVar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:35:33.713616+00:00
-- url     : https://prove2.me/theorems/07e66061-e559-4689-b662-27e8b612036d
-- title:
--   Variance: st Cheb Of Var
-- statement:
--   «and by Chebyshev Pr(Y_{γ,γ'} > U/K² + gP/K³) ≤ 4K⁶/g», from Var Y ≤ 4PU and U ≤ gP: the
--   deviation is gP/K³, so the bound is 4gP²·K⁶/(gP)². The proof is that of `Eight.SecNetworks.cheb_Y`,
--   from the two hypotheses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L66-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L66-L89

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

theorem Variance.stChebOfVar : StChebOfVar := by sorry
