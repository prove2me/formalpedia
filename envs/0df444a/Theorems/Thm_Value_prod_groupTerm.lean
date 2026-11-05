-- Prove2me | Theorems.Thm_Value_prod_groupTerm
-- name    : Value.prod_groupTerm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:03:49.993284+00:00
-- url     : https://prove2.me/theorems/f3582b5b-87b6-430f-9f35-2d74a2e074ee
-- title:
--   Value: prod group Term
-- statement:
--   The product over the groups of the terms of the tables is the term of (z, θ) in the joint sum:
--   every node lies in one group; a pair of nodes in the same group lies inside one group; a pair {a, b}
--   of nodes in different groups occurs twice, as (a, b) in the table of a's group and as (b, a) in the
--   table of b's group, with the same string θ_{a,b}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Joint.lean#L60-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Joint.lean#L60-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Blocks
import Definitions.Def_Value_Sums
import Definitions.Def_Value_Joint
set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}

theorem Value.prod_groupTerm (N : Net g) (χ : Fin g → Fin K) (z : Fin g → List Bool) (θ : Fin g × Fin g → List Bool) :
    ∏ γ, groupTerm N χ θ γ (fun a => if χ a = γ then z a else []) = jointTerm N χ z θ := by sorry
