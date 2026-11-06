-- Prove2me | Theorems.Thm_SparsificationLemma_Gen_occN_out_le
-- name    : SparsificationLemma.Gen.occN_out_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:52:51.930602+00:00
-- url     : https://prove2.me/theorems/f8bb99d5-8064-42a6-9568-ebf3307355ee
-- title:
--   Gen: occ N out le
-- statement:
--   A variable occurs in at most as many clauses of `out x` as of `leafM x`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Gen.lean#L121-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Gen.lean#L121-L122

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

theorem SparsificationLemma.Gen.occN_out_le (x : CNode) (v : ℕ) : occN (out x) v ≤ occN (leafM x) v := by sorry
