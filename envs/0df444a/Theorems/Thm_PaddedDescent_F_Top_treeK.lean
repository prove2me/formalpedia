-- Prove2me | Theorems.Thm_PaddedDescent_F_Top_treeK
-- name    : PaddedDescent.F.Top.treeK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:54.730197+00:00
-- url     : https://prove2.me/theorems/7b162825-5b76-496e-b838-9af66af17fad
-- title:
--   Top: tree K
-- statement:
--   The sparsification tree of a formula ψ of at most m clauses of 1 to k literals on variables
--   below n: every node that `leaves` returns at depth bsum τ k · n is a leaf (`stepK` gives `none` on
--   it); their number; the word of
--   every state of the walk is short; and if the test is right on every formula of at most (leafC τ k + 2)·n
--   clauses of 1 to k literals in which every variable occurs at most
--   leafC τ k + 2 times, then some leaf passes the test iff ψ is satisfiable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L114-L149
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Top.lean#L114-L149

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_NSat
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_PaddedDescent_F_Top
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Top
open Finset Groundwork Groundwork.Prog
open Groundwork.Sparsify (PFml leaves rootP roundB round)
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (WfL occ nSat)

theorem PaddedDescent.F.Top.treeK (hLf : StLeaf) {k τ n m : ℕ} (hτ : 1 ≤ τ) (ψ : Fml) (hψl : ψ.length ≤ m)
    (hψne : ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (test : PFml → Bool)
    (htest : ∀ x : Fml, x.length ≤ (leafC τ k + 2) * n → WfL k n [x] → (∀ v, (occ x v).length ≤ leafC τ k + 2) →
      (test x = true ↔ Fml.Sat x)) :
    (∀ x ∈ leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ), stepK (theta τ) k x = none) ∧
    (leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ)).length ≤ ∑ j ∈ range (k * n / τ + 1), (bsum τ k * n).choose j ∧
    (∀ i, len ((roundB (stepK (theta τ) k) test)^[i] ([rootP ψ], false)) ≤ stackLen k τ n m) ∧
    ((leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ)).any test = true ↔ Fml.Sat ψ) := by sorry
