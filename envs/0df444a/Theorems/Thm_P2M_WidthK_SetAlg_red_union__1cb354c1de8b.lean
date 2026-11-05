-- Prove2me | Theorems.Thm_P2M_WidthK_SetAlg_red_union__1cb354c1de8b
-- name    : P2M_WidthK_SetAlg_red_union__1cb354c1de8b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:05:50.35398+00:00
-- url     : https://prove2.me/theorems/e872afcc-9fb3-4894-a46f-02344e9402a8
-- title:
--   P2 M Width K Set Alg red union  1cb354c1de8b: P2 M Width K Set Alg red union  1cb354c1de8b
-- statement:
--   Let no clause of F contain another, and add a set A of proper subsets of clauses of F, none of
--   which contains another. Then the
--   inclusion-minimal clauses of F ∪ A are those of A and the clauses of F that contain no member of A.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L31-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/SetAlg.lean#L31-L52

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

theorem P2M_WidthK_SetAlg_red_union__1cb354c1de8b {F A : Finset (Finset α)} (hF : Reduced F) (hss : ∀ D ∈ A, ∃ C ∈ F, D ⊂ C)
    (hanti : ∀ D ∈ A, ∀ E ∈ A, D ⊆ E → D = E) : red (F ∪ A) = A ∪ F.filter fun C => ∀ D ∈ A, ¬ D ⊆ C := by sorry

alias «WidthK».«SetAlg».«red_union'» := P2M_WidthK_SetAlg_red_union__1cb354c1de8b
