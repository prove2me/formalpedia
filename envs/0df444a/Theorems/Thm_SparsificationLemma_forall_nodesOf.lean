-- Prove2me | Theorems.Thm_SparsificationLemma_forall_nodesOf
-- name    : SparsificationLemma.forall_nodesOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:53:45.029062+00:00
-- url     : https://prove2.me/theorems/055a375f-a52a-44cb-932c-bdfecfb482cc
-- title:
--   Sparsification Lemma: forall nodes Of
-- statement:
--   What holds at s and passes from a node to its two children holds at all nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Nodes.lean#L61-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Nodes.lean#L61-L73

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
import Theorems.Thm_WidthK_InvK_step
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
variable {σ : Type} (step : σ → Option (σ × σ))

theorem SparsificationLemma.forall_nodesOf {I : σ → Prop} (hI : ∀ s l h, I s → step s = some (l, h) → I l ∧ I h) (d : ℕ) (s : σ) (hs : I s) : ∀ x ∈ nodesOf step d s, I x := by sorry
