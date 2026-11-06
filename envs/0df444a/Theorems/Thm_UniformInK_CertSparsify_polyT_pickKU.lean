-- Prove2me | Theorems.Thm_UniformInK_CertSparsify_polyT_pickKU
-- name    : UniformInK.CertSparsify.polyT_pickKU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:53:06.002211+00:00
-- url     : https://prove2.me/theorems/eaeeb06c-0c9d-4454-869a-6dfc9bf4aba8
-- title:
--   Cert Sparsify: poly T pick KU
-- statement:
--   The choice of the heart and its petals at a node is polynomial-time jointly in k, τ and the
--   formula, if k and 2^k are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L147-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L147-L150

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

theorem UniformInK.CertSparsify.polyT_pickKU {k τ : α → ℕ} {s : α → PFml} (hk : Unary k) (h2 : Unary fun x => 2 ^ k x) (hτ : PolyT τ) (hs : PolyT s) :
    PolyT fun x => pickK (thetaU (τ x)) (k x) (s x) := by sorry
