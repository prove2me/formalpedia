-- Prove2me | Theorems.Thm_UniformInK_CertSparsify_le_of_mem_pairsK
-- name    : UniformInK.CertSparsify.le_of_mem_pairsK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:42:37.134956+00:00
-- url     : https://prove2.me/theorems/41299f4e-3abf-4bb8-b2db-5752412b3f4f
-- title:
--   Cert Sparsify: le of mem pairs K
-- statement:
--   In a pair (j, h) of the list, j is at most k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L78-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L78-L83

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

theorem UniformInK.CertSparsify.le_of_mem_pairsK {k : ℕ} {jh : ℕ × ℕ} (h : jh ∈ pairsK k) : jh.1 ≤ k := by sorry
