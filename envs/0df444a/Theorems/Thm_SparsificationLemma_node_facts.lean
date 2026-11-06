-- Prove2me | Theorems.Thm_SparsificationLemma_node_facts
-- name    : SparsificationLemma.node_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:53:45.836339+00:00
-- url     : https://prove2.me/theorems/f29ef66c-219d-47fa-bee7-bc5f1593da82
-- title:
--   Sparsification Lemma: node facts
-- statement:
--   At every node of the tree of a k-CNF ψ on n variables, for thresholds with `ThrC`: the formula
--   is in normal form, none of its clauses contains another, it is a k-CNF on n variables, and it has at
--   most as many clauses as ψ;
--   every side clause has one literal, on a variable below n; and the side list, as a list, has at most
--   k·(k−1)·n/τ clauses: only a step to a second child lengthens it, by at most k clauses, and a path
--   has at most (k−1)·n/τ such steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Nodes.lean#L85-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Nodes.lean#L85-L127

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_StepSparsifyDefs
import Definitions.Def_SparsificationLemma_Iface
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_SparsificationLemma_Nodes
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK

theorem SparsificationLemma.node_facts {k τ n : ℕ} {θ β : ℕ → ℕ} {ψ : PFml} (hT : ThrC k τ θ β) (hψ : IsKCNF k n ψ) (D : ℕ) :
    ∀ x ∈ nodesOf (stepC θ k) D (root ψ), NF x.1 ∧ Reduced (toFin x.1) ∧ IsKCNF k n x.1 ∧ x.1.length ≤ ψ.length ∧ (∀ C ∈ x.2, ∃ l, C = [l] ∧ l.1 < n) ∧
      x.2.length * τ ≤ k * ((k - 1) * n) := by sorry
