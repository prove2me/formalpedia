-- Prove2me | Theorems.Thm_P2M_ClauseBound_Grid_card___pd_ac2b31513cb7
-- name    : P2M_ClauseBound_Grid_card___pd_ac2b31513cb7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:02.973066+00:00
-- url     : https://prove2.me/theorems/25af3f25-0740-453c-8398-337f75f0dc00
-- title:
--   P2 M Clause Bound Grid card   pd ac2b31513cb7: P2 M Clause Bound Grid card   pd ac2b31513cb7
-- statement:
--   The number of rectangles of a grid with p rows and d columns is C(p,2)·C(d,2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L127-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L127-L130

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]

theorem P2M_ClauseBound_Grid_card___pd_ac2b31513cb7 {p d : ℕ} (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d) : #(Ω ρ γ) = p.choose 2 * d.choose 2 := by sorry

alias «ClauseBound».«Grid».«card_Ω_pd» := P2M_ClauseBound_Grid_card___pd_ac2b31513cb7
