-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_clAt_polyT
-- name    : PaddedDescent.F.Mark.Cert.clAt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:19:57.29722+00:00
-- url     : https://prove2.me/theorems/c681395d-c336-4451-8ba6-14118e70ec2a
-- title:
--   Cert: cl At poly T
-- statement:
--   Clause number e with the index of its layer.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L41-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L41-L42

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

theorem PaddedDescent.F.Mark.Cert.clAt_polyT {Ls : α → List Fml} {e : α → ℕ} (hL : PolyT Ls) (he : PolyT e) : PolyT fun x => clAt (Ls x) (e x) := by sorry
