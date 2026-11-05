-- Prove2me | Theorems.Thm_Value_prod_inside
-- name    : Value.prod_inside
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:00:59.620336+00:00
-- url     : https://prove2.me/theorems/ab9605df-ca88-49e2-bc45-d986e54ef2db
-- title:
--   Value: prod inside
-- statement:
--   The pairs {a, b} inside the group γ, over all γ, are the pairs of nodes in the same group.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Sums.lean#L60-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Sums.lean#L60-L65

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

theorem Value.prod_inside (χ : Fin g → Fin K) (F : Fin g × Fin g → ℤ) :
    ∏ γ, ∏ p ∈ pairs (Fin g) with χ p.1 = γ ∧ χ p.2 = γ, F p = ∏ p ∈ pairs (Fin g) with χ p.1 = χ p.2, F p := by sorry
