-- Prove2me | Theorems.Thm_Variance_sum_ordered
-- name    : Variance.sum_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:33:29.595701+00:00
-- url     : https://prove2.me/theorems/b14d081a-b794-446d-a47d-c9149b12892d
-- title:
--   Variance: sum ordered
-- statement:
--   A sum over the ordered pairs of distinct nodes, as a double sum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Cov.lean#L30-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Variance/Cov.lean#L30-L38

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

theorem Variance.sum_ordered {g : ℕ} {X : Type} [AddCommMonoid X] (F : Fin g × Fin g → X) : ∑ p ∈ ordered g, F p = ∑ a, ∑ b ∈ univ.erase a, F (a, b) := by sorry
