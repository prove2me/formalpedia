-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_tchB_polyT
-- name    : PaddedDescent.F.Mark.Cert.tchB_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:21:21.885965+00:00
-- url     : https://prove2.me/theorems/5802fd21-724c-4148-aa9f-df5b8a2b99f4
-- title:
--   Cert: tch B poly T
-- statement:
--   The test «clause e touches node a».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L45-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L45-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_PaddedDescent_F_CertMark
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Cert
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]

theorem PaddedDescent.F.Mark.Cert.tchB_polyT {g n a e : α → ℕ} {Ls : α → List Fml} (hg : PolyT g) (hn : PolyT n) (hL : PolyT Ls) (ha : PolyT a)
    (he : PolyT e) : PolyT fun x => tchB (g x) (n x) (Ls x) (a x) (e x) := by sorry
