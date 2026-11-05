-- Prove2me | Theorems.Thm_StepSparsify_thrListCal_polyT
-- name    : StepSparsify.thrListCal_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:54:18.903244+00:00
-- url     : https://prove2.me/theorems/cc8c4330-9c0f-489f-9d84-d6089eb52ed5
-- title:
--   Step Sparsify: thr List Cal poly T
-- statement:
--   The list of the pairs (j, h), each with Calabro's threshold θ (j - h), is polynomial-time
--   jointly in k and s, both given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalServes.lean#L55-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/CalServes.lean#L55-L63

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open StepSparsify
open Finset Groundwork Groundwork.Sparsify WidthK.Prog CountKSat CountKSat.Poly PaddedDescent UniformInK UniformInK.CertSparsify SparsificationLemma
variable {α : Type} [Enc α]

theorem StepSparsify.thrListCal_polyT (hT : StCertThCal) {k s : α → ℕ} (hk : Unary k) (hs : Unary s) :
    PolyT fun x => (pairsK (k x)).map fun jh => (jh, thCal (k x) (s x) (jh.1 - jh.2)) := by sorry
