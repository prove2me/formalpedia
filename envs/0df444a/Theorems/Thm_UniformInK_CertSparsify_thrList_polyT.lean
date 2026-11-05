-- Prove2me | Theorems.Thm_UniformInK_CertSparsify_thrList_polyT
-- name    : UniformInK.CertSparsify.thrList_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T19:42:12.783223+00:00
-- url     : https://prove2.me/theorems/db5d0e8a-c4cc-4de6-915b-71ea40d9032f
-- title:
--   Cert Sparsify: thr List poly T
-- statement:
--   The list of the pairs (j, h), each with its threshold θ (j - h), is polynomial-time jointly in τ
--   and k, if k is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L100-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L100-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_UniformInK_Cert_Sparsify
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open UniformInK UniformInK.CertSparsify
open Groundwork Groundwork.Sparsify WidthK.Prog
variable {α : Type} [Enc α]

theorem UniformInK.CertSparsify.thrList_polyT {k τ : α → ℕ} (hk : Unary k) (hτ : PolyT τ) :
    PolyT fun x => (pairsK (k x)).map fun jh => (jh, thetaU (τ x) (jh.1 - jh.2)) := by sorry
