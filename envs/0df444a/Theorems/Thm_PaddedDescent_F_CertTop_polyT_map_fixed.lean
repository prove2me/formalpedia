-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_polyT_map_fixed
-- name    : PaddedDescent.F.CertTop.polyT_map_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:16:14.08549+00:00
-- url     : https://prove2.me/theorems/5e8730dd-f2a6-411d-9c94-586a1550baea
-- title:
--   Cert Top: poly T map fixed
-- statement:
--   A list of fixed length whose members are polynomial-time functions of x is a polynomial-time
--   function of x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSparsify.lean#L36-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSparsify.lean#L36-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_PaddedDescent_F_CertSparsify
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_WidthK_Prog_pickK_eq
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open Groundwork Groundwork.Sparsify
open WidthK (thrPair theta)
open WidthK.Prog (pairsK pickK pickK_eq stepK)
variable {α σ : Type} [Enc α] [Enc σ]
omit [Enc σ]

theorem PaddedDescent.F.CertTop.polyT_map_fixed {β γ : Type} [Enc γ] (l : List β) {f : β → α → γ} (hf : ∀ b, PolyT (f b)) :
    PolyT fun x => l.map fun b => f b x := by sorry
