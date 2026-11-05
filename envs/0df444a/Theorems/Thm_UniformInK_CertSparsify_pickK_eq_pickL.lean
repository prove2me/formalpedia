-- Prove2me | Theorems.Thm_UniformInK_CertSparsify_pickK_eq_pickL
-- name    : UniformInK.CertSparsify.pickK_eq_pickL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:43:03.522166+00:00
-- url     : https://prove2.me/theorems/7cada003-713d-4b77-917b-0189660cfe95
-- title:
--   Cert Sparsify: pick K eq pick L
-- statement:
--   `pickK` is `pickL` at the two lists that belong to θ and k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L125-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Sparsify.lean#L125-L126

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

theorem UniformInK.CertSparsify.pickK_eq_pickL (θ : ℕ → ℕ) (k : ℕ) (s : PFml) :
    pickK θ k s = pickL (masks k) ((pairsK k).map fun jh => (jh, θ (jh.1 - jh.2))) s := by sorry
