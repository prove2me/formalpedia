-- Prove2me | Theorems.Thm_UniformInK_CertSparsify_pairsK_polyT
-- name    : UniformInK.CertSparsify.pairsK_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:42:22.609213+00:00
-- url     : https://prove2.me/theorems/787c291a-316e-4f0c-970f-6a2dd8ac44d2
-- title:
--   Cert Sparsify: pairs K poly T
-- statement:
--   The list of the pairs (j, h) with 1 ≤ h < j ≤ k is polynomial-time if k is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L65-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L65-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_UniformInK_Cert_Sparsify
set_option autoImplicit false
section
section
open UniformInK UniformInK.CertSparsify
open Groundwork Groundwork.Sparsify WidthK.Prog
variable {α : Type} [Enc α]

theorem UniformInK.CertSparsify.pairsK_polyT {k : α → ℕ} (hk : Unary k) : PolyT fun x => pairsK (k x) := by sorry
