-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_ownB_polyT
-- name    : PaddedDescent.F.Mark.Cert.ownB_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:22:47.164847+00:00
-- url     : https://prove2.me/theorems/8183e9b9-e0af-402e-a977-e0bb719883ab
-- title:
--   Cert: own B poly T
-- statement:
--   The test «a is the least node that clause e touches».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L63-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L63-L66

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

theorem PaddedDescent.F.Mark.Cert.ownB_polyT {g n e a : α → ℕ} {Ls : α → List Fml} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls) (he : PolyT e)
    (ha : PolyT a) : PolyT fun x => ownB (g x) (n x) (Ls x) (e x) (a x) := by sorry
