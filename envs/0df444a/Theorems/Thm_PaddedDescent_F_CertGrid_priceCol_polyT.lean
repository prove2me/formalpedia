-- Prove2me | Theorems.Thm_PaddedDescent_F_CertGrid_priceCol_polyT
-- name    : PaddedDescent.F.CertGrid.priceCol_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:11:09.365205+00:00
-- url     : https://prove2.me/theorems/43d128c4-521f-40c3-9b4a-96bf20c6c8d8
-- title:
--   Cert Grid: price Col poly T
-- statement:
--   The price of a pattern with the columns merged is polynomial-time, for g and the label length in
--   unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L78-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertGrid.lean#L78-L86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_PaddedDescent_F_CertGrid
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertGrid
open Groundwork Groundwork.Prog
variable {α : Type} [Enc α]

theorem PaddedDescent.F.CertGrid.priceCol_polyT {g n y : α → ℕ} (hg : Unary g) (hn : Unary n) (hy : PolyT y) :
    PolyT fun x => priceCol (g x) (n x) (y x) := by sorry
