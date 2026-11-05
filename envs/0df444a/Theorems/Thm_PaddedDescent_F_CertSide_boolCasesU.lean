-- Prove2me | Theorems.Thm_PaddedDescent_F_CertSide_boolCasesU
-- name    : PaddedDescent.F.CertSide.boolCasesU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:18:31.558437+00:00
-- url     : https://prove2.me/theorems/1fb3c23f-fb5c-49e3-aa47-f0411052f4e1
-- title:
--   Cert Side: bool Cases U
-- statement:
--   The same for lengths given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L34-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L34-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_PaddedDescent_F_CertSide
set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertSide
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]

theorem PaddedDescent.F.CertSide.boolCasesU {F : Bool → α → ℕ} (h : ∀ b, Unary (F b)) {tr : α → Bool} (ht : PolyT tr) : Unary fun x => F (tr x) x := by sorry
