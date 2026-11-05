-- Prove2me | Theorems.Thm_Variance_sum_ordered_c
-- name    : Variance.sum_ordered_c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:22:36.168069+00:00
-- url     : https://prove2.me/theorems/f6988fe7-0493-4d1c-afda-14721c852bf1
-- title:
--   Variance: sum ordered c
-- statement:
--   The total U is the sum of c_{a,b} over the ordered pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Cov.lean#L41-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Cov.lean#L41-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Variance_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Variance_Cov
set_option autoImplicit false
section
section
open Variance
open Finset Eight.SecNetworks

theorem Variance.sum_ordered_c {g : ℕ} (c : Fin g → Fin g → ℕ) : ∑ p ∈ ordered g, c p.1 p.2 = ∑ a, ∑ b ∈ univ.erase a, c a b := by sorry
