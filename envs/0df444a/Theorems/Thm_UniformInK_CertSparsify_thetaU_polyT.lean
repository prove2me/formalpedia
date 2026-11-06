-- Prove2me | Theorems.Thm_UniformInK_CertSparsify_thetaU_polyT
-- name    : UniformInK.CertSparsify.thetaU_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:52:55.497758+00:00
-- url     : https://prove2.me/theorems/89e3cd5f-7583-4622-9f24-f5da5d344fd1
-- title:
--   Cert Sparsify: theta U poly T
-- statement:
--   The threshold θ i is polynomial-time jointly in τ and i, if i is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L92-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L92-L96

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

theorem UniformInK.CertSparsify.thetaU_polyT {τ i : α → ℕ} (hτ : PolyT τ) (hi : Unary i) : PolyT fun x => thetaU (τ x) (i x) := by sorry
