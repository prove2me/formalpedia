-- Prove2me | Theorems.Thm_WidthK_SetAlg_light_eq
-- name    : WidthK.SetAlg.light_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:41:57.293599+00:00
-- url     : https://prove2.me/theorems/b578b4f7-66d1-4251-84f8-cff96893af2e
-- title:
--   Set Alg: light eq
-- statement:
--   The light child consists of the heart H and the clauses of F that do not contain H.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L77-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L77-L87

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

theorem WidthK.SetAlg.light_eq (hθ : ∀ i, 1 ≤ θ i) (hF : Reduced F) (h : Heart θ F j H) :
    light F H = {H} ∪ F.filter fun C => ¬ H ⊆ C := by sorry
