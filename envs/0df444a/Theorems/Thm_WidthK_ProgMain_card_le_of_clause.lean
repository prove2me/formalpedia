-- Prove2me | Theorems.Thm_WidthK_ProgMain_card_le_of_clause
-- name    : WidthK.ProgMain.card_le_of_clause
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:40:42.329899+00:00
-- url     : https://prove2.me/theorems/153cdb78-e213-4a44-9b24-efcd8e10050f
-- title:
--   Prog Main: card le of clause
-- statement:
--   If every clause of F lies inside a clause of F₀, and these have at most k literals, then F has
--   at most |F₀|·2^k clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L126-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/ProgMain.lean#L126-L134

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_ProgMain
set_option autoImplicit false
section
section
open WidthK WidthK.ProgMain
open Finset Groundwork Groundwork.Sparsify WidthK.Prog
variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

theorem WidthK.ProgMain.card_le_of_clause {F₀ F : Finset (Finset PLit)} (hk : ∀ C ∈ F₀, C.card ≤ k) (h : ∀ C ∈ F, ∃ C₀ ∈ F₀, C ⊆ C₀) :
    F.card ≤ F₀.card * 2 ^ k := by sorry
