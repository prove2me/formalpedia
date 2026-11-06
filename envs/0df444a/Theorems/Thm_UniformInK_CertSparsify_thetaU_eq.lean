-- Prove2me | Theorems.Thm_UniformInK_CertSparsify_thetaU_eq
-- name    : UniformInK.CertSparsify.thetaU_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:52:21.349576+00:00
-- url     : https://prove2.me/theorems/652b5aab-656e-4736-af81-baa831546cb6
-- title:
--   Cert Sparsify: theta U eq
-- statement:
--   `thetaU τ i` as one expression: 1 if i = 0, otherwise 4·τ^(2i−1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L86-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L86-L89

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

theorem UniformInK.CertSparsify.thetaU_eq (τ i : ℕ) : thetaU τ i = if i = 0 then 1 else 4 * τ ^ (2 * i - 1) := by sorry
