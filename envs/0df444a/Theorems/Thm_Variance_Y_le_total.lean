-- Prove2me | Theorems.Thm_Variance_Y_le_total
-- name    : Variance.Y_le_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:05:16.551195+00:00
-- url     : https://prove2.me/theorems/d2b38825-848b-4a7a-aa89-75873bf13b25
-- title:
--   Variance: Y le total
-- statement:
--   Y_{γ,γ'} ≤ U: a sum over some of the ordered pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L56-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Grouping.lean#L56-L61

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

theorem Variance.Y_le_total {g K : ℕ} (c : Fin g → Fin g → ℕ) (χ : Fin g → Fin K) {γ γ' : Fin K} (hne : γ ≠ γ') : Y c χ γ γ' ≤ ∑ a, ∑ b ∈ univ.erase a, c a b := by sorry
