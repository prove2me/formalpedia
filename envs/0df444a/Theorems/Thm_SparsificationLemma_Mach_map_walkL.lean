-- Prove2me | Theorems.Thm_SparsificationLemma_Mach_map_walkL
-- name    : SparsificationLemma.Mach.map_walkL
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:02:41.926698+00:00
-- url     : https://prove2.me/theorems/2e3ab079-b7d5-46c4-8691-e645ac46eb78
-- title:
--   Mach: map walk L
-- statement:
--   For k ≥ 1, τ ≥ k², τ ≥ 8k and a k-CNF ψ on n variables: if L is at least Σ_{j ≤ kn/τ} C(bsumU τ
--   k · n, j), which bounds the number of leaves, and the pad has at least 2L − 1 units and at least
--   L·(nodeLen k n m + 2) + 6 units, m the number of clauses of ψ, then the walk returns nodes whose
--   outputs are `outTau k n τ ψ`, and every variable of the outputs is below n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Len.lean#L77-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Mach/Len.lean#L77-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Walk
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_UniformInK_Tree_Tree
import Definitions.Def_UniformInK_Spars_Main
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Definitions.Def_SparsificationLemma_Mach_Len
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Mach
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSatRate UniformInK PaddedDescent PaddedDescent.F ClauseBound.Alg SparsificationLemma.Geo

theorem SparsificationLemma.Mach.map_walkL {k τ n L : ℕ} {ψ : PFml} {pad : U} (hk : 1 ≤ k) (h2 : k ^ 2 ≤ τ) (h8 : 8 * k ≤ τ) (hψ : IsKCNF k n ψ)
    (hL : ∑ j ∈ Finset.range (k * n / τ + 1), (bsumU τ k * n).choose j ≤ L) (hp1 : 2 * L ≤ pad.length + 1) (hp2 : L * (nodeLen k n ψ.length + 2) + 6 ≤ pad.length) :
    (walkL k pad τ (rootC (List.replicate n (), ψ))).map out = outTau k n τ ψ ∧ ∀ Φ ∈ outTau k n τ ψ, ∀ C ∈ Φ, ∀ l ∈ C, l.1 < n := by sorry
