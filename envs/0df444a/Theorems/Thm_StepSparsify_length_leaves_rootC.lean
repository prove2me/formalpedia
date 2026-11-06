-- Prove2me | Theorems.Thm_StepSparsify_length_leaves_rootC
-- name    : StepSparsify.length_leaves_rootC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:52:59.705678+00:00
-- url     : https://prove2.me/theorems/0a253945-5f59-4744-a2b3-5cc9389766e6
-- title:
--   Step Sparsify: length leaves root C
-- statement:
--   The tree that starts with the n clauses xᵢ ∨ ¬xᵢ on the side list has as many leaves as the tree
--   that starts with the empty side list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalServes.lean#L46-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalServes.lean#L46-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_StepSparsify_CalNumbers
import Definitions.Def_StepSparsify_CalLeaves
import Definitions.Def_StepSparsify_CertThCal
import Definitions.Def_SparsificationLemma_Cal_Thr
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Gen
import Definitions.Def_UniformInK_Cert_Sparsify
import Definitions.Def_CountKSat_Poly
import Definitions.Def_StepSparsify_CalServes
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent UniformInK UniformInK.CertSparsify SparsificationLemma

theorem StepSparsify.length_leaves_rootC (θ : ℕ → ℕ) (k D n : ℕ) (ψ : PFml) :
    (leaves (stepC θ k) D (rootC (List.replicate n (), ψ))).length = (tree θ k D ψ).length := by sorry
