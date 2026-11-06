-- Prove2me | Theorems.Thm_SparsificationLemma_length_sideU_le
-- name    : SparsificationLemma.length_sideU_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:54:29.219568+00:00
-- url     : https://prove2.me/theorems/84dcf2e2-841c-4baa-984b-6d82496ee971
-- title:
--   Sparsification Lemma: length side U le
-- statement:
--   There are only 2n clauses with one literal: the side list as it is written in the output has at
--   most 2n clauses, if its variables are below n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Nodes.lean#L133-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Nodes.lean#L133-L142

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
import Theorems.Thm_CountKSatRate_Leaf_length_sideU_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK

theorem SparsificationLemma.length_sideU_le {X : PFml} {n : ℕ} (h : ∀ C ∈ X, ∀ l ∈ C, l.1 < n) : (sideU X).length ≤ 2 * n := by sorry
