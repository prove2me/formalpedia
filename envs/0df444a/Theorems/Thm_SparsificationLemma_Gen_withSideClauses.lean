-- Prove2me | Theorems.Thm_SparsificationLemma_Gen_withSideClauses
-- name    : SparsificationLemma.Gen.withSideClauses
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:07:37.682937+00:00
-- url     : https://prove2.me/theorems/ba0dbbb2-2474-494b-ad35-2c036a973485
-- title:
--   Gen: with Side Clauses
-- statement:
--   The tree whose side list starts with the clauses xᵢ ∨ ¬xᵢ, for thresholds with `ThrC`, τ ≥ 1 and
--   D ≥ (β 0 + … + β (k-1))·n. B is any bound for the side list: n·τ + k·(k−1)·n ≤ B·τ.
--   The number of leaves; what holds at a leaf; the stack of the depth-first walk.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Gen.lean#L69-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Gen.lean#L69-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSatRate_Tree
import Definitions.Def_SparsificationLemma_Iface
import Definitions.Def_SparsificationLemma_Shrink
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_PaddedDescent_F_MarkDeg
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Gen
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)
open SparsificationLemma.Gen
variable {k τ n D : ℕ} {θ β : ℕ → ℕ} {ψ : PFml}

theorem SparsificationLemma.Gen.withSideClauses (hτ : 1 ≤ τ) (hT : ThrC k τ θ β) (hD : (∑ i ∈ range k, β i) * n ≤ D) (hψ : IsKCNF k n ψ) {B : ℕ}
    (hB : n * τ + k * ((k - 1) * n) ≤ B * τ) :
    (leaves (stepC θ k) D (rootP ψ, taut n)).length ≤ ∑ j ∈ range ((k - 1) * n / τ + 1), D.choose j ∧
    (∀ x ∈ leaves (stepC θ k) D (rootP ψ, taut n),
      stepC θ k x = none ∧ (leafF x).length ≤ (2 * ∑ j ∈ range k, θ j) * n + B ∧
        (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ v, (occ x.1 v).length ≤ 2 * ∑ j ∈ range k, θ j) ∧
        (∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) ∧ x.1.length ≤ ψ.length) ∧
    ∀ i, ((round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1,
        x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ B ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n := by sorry
