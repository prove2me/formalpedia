-- Prove2me | Theorems.Thm_P2M_ClauseBound_Grid_filter_mem___5a0745b93ff2
-- name    : P2M_ClauseBound_Grid_filter_mem___5a0745b93ff2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:12.814263+00:00
-- url     : https://prove2.me/theorems/a14b62c3-05af-4663-a575-e969f5987390
-- title:
--   P2 M Clause Bound Grid filter mem   5a0745b93ff2: P2 M Clause Bound Grid filter mem   5a0745b93ff2
-- statement:
--   The rectangles, as the subset of all ω that lie in Ω.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Expand.lean#L32-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Expand.lean#L32-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_ClauseBound_Grid_Expand
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]

theorem P2M_ClauseBound_Grid_filter_mem___5a0745b93ff2 : (univ.filter fun ω => ω ∈ Ω ρ γ) = Ω ρ γ := by sorry

alias «ClauseBound».«Grid».«filter_mem_Ω» := P2M_ClauseBound_Grid_filter_mem___5a0745b93ff2
