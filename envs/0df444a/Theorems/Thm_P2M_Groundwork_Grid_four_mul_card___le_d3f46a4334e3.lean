-- Prove2me | Theorems.Thm_P2M_Groundwork_Grid_four_mul_card___le_d3f46a4334e3
-- name    : P2M_Groundwork_Grid_four_mul_card___le_d3f46a4334e3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:20:40.730278+00:00
-- url     : https://prove2.me/theorems/3c217fb3-e139-47c0-87f4-92e122e0f4d6
-- title:
--   P2 M Groundwork Grid four mul card   le d3f46a4334e3: P2 M Groundwork Grid four mul card   le d3f46a4334e3
-- statement:
--   4R ≤ g⁴.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Size.lean#L143-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Size.lean#L143-L152

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_Groundwork_Grid_Size
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]

theorem P2M_Groundwork_Grid_four_mul_card___le_d3f46a4334e3 {g : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g) : 4 * #(Ω ρ γ) ≤ g ^ 4 := by sorry

alias «Groundwork».«Grid».«four_mul_card_Ω_le» := P2M_Groundwork_Grid_four_mul_card___le_d3f46a4334e3
