-- Prove2me | Theorems.Thm_UniformInK_CertSparsify_polyT_heartsL
-- name    : UniformInK.CertSparsify.polyT_heartsL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:37:45.269532+00:00
-- url     : https://prove2.me/theorems/9ed13f98-d67e-4fe6-91a3-27f57bb935e2
-- title:
--   Cert Sparsify: poly T hearts L
-- statement:
--   Listing the candidate hearts is polynomial-time jointly in the list of masks, the formula and
--   the sizes j and h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L130-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L130-L132

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

theorem UniformInK.CertSparsify.polyT_heartsL {M : α → List (List Bool)} {s : α → PFml} {j h : α → ℕ} (hM : PolyT M) (hs : PolyT s) (hj : PolyT j)
    (hh : PolyT h) : PolyT fun x => heartsL (M x) (s x) (j x) (h x) := by sorry
