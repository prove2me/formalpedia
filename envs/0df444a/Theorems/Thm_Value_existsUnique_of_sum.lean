-- Prove2me | Theorems.Thm_Value_existsUnique_of_sum
-- name    : Value.existsUnique_of_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:16:29.241879+00:00
-- url     : https://prove2.me/theorems/bfda4751-f35e-408f-b2f0-99c34dc232bd
-- title:
--   Value: exists Unique of sum
-- statement:
--   If Σ_{a ∈ s} F(i a) = Σ_{b ∈ T} F(b) for all F, and exactly one b ∈ T has the property Q, then
--   exactly one a ∈ s is such that i a has the property Q. (With F the indicator of Q both sums count.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Words.lean#L51-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Words.lean#L51-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Words
set_option autoImplicit false
section
section
open Value
open Groundwork Finset

theorem Value.existsUnique_of_sum {α β : Type*} (s : Finset α) (T : Finset β) (i : α → β) (hsum : ∀ F : β → ℤ, ∑ a ∈ s, F (i a) = ∑ b ∈ T, F b)
    (Q : β → Prop) (hQ : ∃! b, b ∈ T ∧ Q b) : ∃! a, a ∈ s ∧ Q (i a) := by sorry
