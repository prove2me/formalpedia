-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_mW2_polyT
-- name    : PaddedDescent.F.Mark.Cert.mW2_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:25:31.820929+00:00
-- url     : https://prove2.me/theorems/9344d9eb-742a-4bda-96d1-c8d2527411f0
-- title:
--   Cert: m W2 poly T
-- statement:
--   The second test of `mW` is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L179-L181
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L179-L181

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

theorem PaddedDescent.F.Mark.Cert.mW2_polyT {g n a : α → ℕ} {Ls : α → List Fml} {z : α → List Bool} (hg : PolyT g) (hn : PolyT n) (hL : PolyT Ls)
    (ha : PolyT a) (hz : PolyT z) : PolyT fun x => mW2 (g x) (n x) (Ls x) (a x) (z x) := by sorry
