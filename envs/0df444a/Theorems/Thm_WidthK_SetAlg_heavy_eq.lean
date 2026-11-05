-- Prove2me | Theorems.Thm_WidthK_SetAlg_heavy_eq
-- name    : WidthK.SetAlg.heavy_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:42:13.454065+00:00
-- url     : https://prove2.me/theorems/ee4c77f1-79ce-404d-a094-43ba18381285
-- title:
--   Set Alg: heavy eq
-- statement:
--   The heavy child consists of the petals and the clauses of F that contain no petal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L90-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L90-L101

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Mathlib.Tactic.Linarith
import Definitions.Def_SparsifyWidthK_SetAlg
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
open WidthK WidthK.SetAlg
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
variable {θ : ℕ → ℕ} {F : Finset (Finset α)} {j : ℕ} {H : Finset α}

theorem WidthK.SetAlg.heavy_eq (hF : Reduced F) (h : Heart θ F j H) :
    heavy F j H = petals F j H ∪ F.filter fun C => ∀ D ∈ petals F j H, ¬ D ⊆ C := by sorry
