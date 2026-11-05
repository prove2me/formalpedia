-- Prove2me | Theorems.Thm_SparsificationLemma_Gen_cntN_leafM
-- name    : SparsificationLemma.Gen.cntN_leafM
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:52:34.505965+00:00
-- url     : https://prove2.me/theorems/aadecf19-57b4-4c37-a40d-167bd655cdac
-- title:
--   Gen: cnt N leaf M
-- statement:
--   `leafM x` and `leafF x` have the same number of satisfying assignments, if every clause of the
--   side list is some xᵢ ∨ ¬xᵢ or has one literal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Gen.lean#L112-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Gen.lean#L112-L114

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
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)
open SparsificationLemma.Gen
variable {k τ n D : ℕ} {θ β : ℕ → ℕ} {ψ : PFml}

theorem SparsificationLemma.Gen.cntN_leafM {x : CNode} (hs : ∀ C ∈ x.2, C ∈ taut n ∨ ∃ l, C = [l]) : cntN n (leafM x) = cntN n (leafF x) := by sorry
