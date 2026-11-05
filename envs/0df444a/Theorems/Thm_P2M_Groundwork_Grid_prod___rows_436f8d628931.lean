-- Prove2me | Theorems.Thm_P2M_Groundwork_Grid_prod___rows_436f8d628931
-- name    : P2M_Groundwork_Grid_prod___rows_436f8d628931
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:30.774387+00:00
-- url     : https://prove2.me/theorems/732fa5e2-004b-4d8c-94d3-7f080b1669f0
-- title:
--   P2 M Groundwork Grid prod   rows 436f8d628931: P2 M Groundwork Grid prod   rows 436f8d628931
-- statement:
--   A product over the rectangles, sorted by pairs of rows. (`to_additive` makes the same lemma for
--   sums, `sum_Ω_rows`.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L106-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L106-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]

theorem P2M_Groundwork_Grid_prod___rows_436f8d628931 {M : Type} [CommMonoid M] (F : Rect ρ γ → M) :
    ∏ ω ∈ Ω ρ γ, F ω = ∏ p ∈ pairs ρ, ∏ k : γ × γ with k.1 < k.2, F (p, k) := by sorry

alias «Groundwork».«Grid».«prod_Ω_rows» := P2M_Groundwork_Grid_prod___rows_436f8d628931
