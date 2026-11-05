-- Prove2me | Theorems.Thm_StepSparsify_polyT_stepCCal
-- name    : StepSparsify.polyT_stepCCal
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:52:20.43441+00:00
-- url     : https://prove2.me/theorems/bca827fe-a981-4381-9333-0ba90f202708
-- title:
--   Step Sparsify: poly T step CCal
-- statement:
--   The two children of a node of the counting tree with Calabro's thresholds are polynomial-time
--   jointly in k, s and the node, if k, 2^k and s are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalServes.lean#L67-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalServes.lean#L67-L73

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
set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent UniformInK UniformInK.CertSparsify SparsificationLemma
variable {α : Type} [Enc α]

theorem StepSparsify.polyT_stepCCal (hT : StCertThCal) {k s : α → ℕ} {x : α → CNode} (hk : Unary k) (h2 : Unary fun a => 2 ^ k a) (hs : Unary s) (hx : PolyT x) :
    PolyT fun a => stepC (thCal (k a) (s a)) (k a) (x a) := by sorry
