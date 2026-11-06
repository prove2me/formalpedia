-- Prove2me | Theorems.Thm_SparsificationLemma_countP_leaves
-- name    : SparsificationLemma.countP_leaves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:51:57.112428+00:00
-- url     : https://prove2.me/theorems/15615f94-caa9-4891-bd11-d719392022eb
-- title:
--   Sparsification Lemma: count P leaves
-- statement:
--   Below a node whose side clauses have one literal each, b satisfies one position of the list of
--   outputs if it satisfies the node, and none otherwise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L121-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/One.lean#L121-L145

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Tauto
import Definitions.Def_SparsificationLemma_One
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate
open CountKSat.StepCount

theorem SparsificationLemma.countP_leaves (θ : ℕ → ℕ) (k D : ℕ) (b : ℕ → Bool) (x : CNode) (hx : ∀ C ∈ x.2, ∃ l, C = [l]) :
    ((leaves (stepC θ k) D x).map out).countP (fun Ψ => decide (Sat b Ψ)) = if Sat b (leafF x) then 1 else 0 := by sorry
