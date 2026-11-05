-- Prove2me | Theorems.Thm_UniformInK_CertSparsify_range_two_mul
-- name    : UniformInK.CertSparsify.range_two_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:51:58.527255+00:00
-- url     : https://prove2.me/theorems/98bab2ae-e342-4c2a-be79-05744dbef9d6
-- title:
--   Cert Sparsify: range two mul
-- statement:
--   The numbers below 2N are 0, 1, then 2, 3, and so on up to 2N-2, 2N-1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L37-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L37-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_UniformInK_Cert_Sparsify
import Theorems.Thm_Groundwork_PolyT_flatMap
attribute [local fun_prop] Groundwork.PolyT.flatMap


set_option autoImplicit false
section
section
open UniformInK UniformInK.CertSparsify
open Groundwork Groundwork.Sparsify WidthK.Prog
variable {α : Type} [Enc α]

theorem UniformInK.CertSparsify.range_two_mul (N : ℕ) : List.range (2 * N) = (List.range N).flatMap fun i => [2 * i, 2 * i + 1] := by sorry
