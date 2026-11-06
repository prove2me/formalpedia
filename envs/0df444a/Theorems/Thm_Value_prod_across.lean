-- Prove2me | Theorems.Thm_Value_prod_across
-- name    : Value.prod_across
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:49.78297+00:00
-- url     : https://prove2.me/theorems/ae856c1f-a1b3-4e20-987d-324492abd457
-- title:
--   Value: prod across
-- statement:
--   The ordered pairs (a, b) with a in the group γ and b outside it, over all γ, are the pairs {a,
--   b} of nodes in different groups, each in both orders.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Sums.lean#L69-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Sums.lean#L69-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Sums
set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Finset Eight.SecNetworks
variable {g K : ℕ}

theorem Value.prod_across (χ : Fin g → Fin K) (F : Fin g × Fin g → ℤ) :
    ∏ γ, ∏ p : Fin g × Fin g with χ p.1 = γ ∧ χ p.2 ≠ γ, F p = ∏ p ∈ pairs (Fin g) with χ p.1 ≠ χ p.2, F p * F p.swap := by sorry
