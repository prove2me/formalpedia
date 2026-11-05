-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_mWs_polyT
-- name    : PaddedDescent.F.Mark.Cert.mWs_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:26:48.109507+00:00
-- url     : https://prove2.me/theorems/b4cfb903-4a85-4508-883f-916f458c76a7
-- title:
--   Cert: m Ws poly T
-- statement:
--   The exponent of the sign in `mW` is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L196-L199
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L196-L199

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

theorem PaddedDescent.F.Mark.Cert.mWs_polyT {g n a : α → ℕ} {Ls : α → List Fml} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls)
    (ha : PolyT a) (hz : PolyT z) : PolyT fun x => mWs (g x) (n x) (Ls x) (a x) (z x) := by sorry
