-- Prove2me | Theorems.Thm_UniformInK_CertSparsify_masks_eq
-- name    : UniformInK.CertSparsify.masks_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:51:42.230039+00:00
-- url     : https://prove2.me/theorems/59009123-9291-498a-ac81-560e03beebd4
-- title:
--   Cert Sparsify: masks eq
-- statement:
--   The list `masks k` consists of the words of k bits of the numbers 0, 1, …, 2^k - 1, lowest bit
--   first.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L46-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L46-L53

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

theorem UniformInK.CertSparsify.masks_eq (k : ℕ) : masks k = (List.range (2 ^ k)).map (toWord k) := by sorry
