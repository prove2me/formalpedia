-- Prove2me | Theorems.Thm_PaddedDescent_F_CertSide_boolCases
-- name    : PaddedDescent.F.CertSide.boolCases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:41:50.841002+00:00
-- url     : https://prove2.me/theorems/7e8983dd-89f9-43c6-832f-2a90d1ef8313
-- title:
--   Cert Side: bool Cases
-- statement:
--   A function with a truth value as a parameter is polynomial-time in that parameter too, if it is
--   for both of its values.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L29-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertSide.lean#L29-L31

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

theorem PaddedDescent.F.CertSide.boolCases {β : Type} [Enc β] {F : Bool → α → β} (h : ∀ b, PolyT (F b)) {tr : α → Bool} (ht : PolyT tr) :
    PolyT fun x => F (tr x) x := by sorry
