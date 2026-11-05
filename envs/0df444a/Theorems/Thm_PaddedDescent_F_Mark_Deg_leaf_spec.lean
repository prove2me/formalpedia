-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Deg_leaf_spec
-- name    : PaddedDescent.F.Mark.Deg.leaf_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:26:24.929965+00:00
-- url     : https://prove2.me/theorems/2e482df3-39b5-4d5c-9145-7c074fbcbe06
-- title:
--   Deg: leaf spec
-- statement:
--   Every leaf of the tree of `stepK (theta τ) k` below `rootP ψ` is in normal form, has nonempty
--   clauses only, and every variable occurs in at most leafC τ k of
--   its clauses. ψ has variables below n and nonempty clauses of at most k literals.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L113-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkDeg.lean#L113-L141

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_PaddedDescent_F_MarkDeg
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Deg
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify
open WidthK (theta bsum leafC lay)
open WidthK.Prog (stepK NF toFin)

theorem PaddedDescent.F.Mark.Deg.leaf_spec {τ : ℕ} (hτ : 1 ≤ τ) (k n : ℕ) (ψ : PFml) (hψ : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    ∀ x ∈ leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ), NF x ∧ (∀ C ∈ x, C ≠ []) ∧ ∀ v, (occ x v).length ≤ leafC τ k := by sorry
