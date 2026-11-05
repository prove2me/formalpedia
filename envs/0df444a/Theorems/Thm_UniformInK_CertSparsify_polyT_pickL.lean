-- Prove2me | Theorems.Thm_UniformInK_CertSparsify_polyT_pickL
-- name    : UniformInK.CertSparsify.polyT_pickL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:37:53.750255+00:00
-- url     : https://prove2.me/theorems/1fb1fece-b415-463e-ab78-edc9cf66c874
-- title:
--   Cert Sparsify: poly T pick L
-- statement:
--   The choice of the heart and its petals is polynomial-time jointly in the two lists.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L141-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L141-L143

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

theorem UniformInK.CertSparsify.polyT_pickL {M : α → List (List Bool)} {L : α → List ((ℕ × ℕ) × ℕ)} {s : α → PFml} (hM : PolyT M) (hL : PolyT L)
    (hs : PolyT s) : PolyT fun x => pickL (M x) (L x) (s x) := by sorry
