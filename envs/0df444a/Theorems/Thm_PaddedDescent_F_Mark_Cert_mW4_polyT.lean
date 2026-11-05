-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_mW4_polyT
-- name    : PaddedDescent.F.Mark.Cert.mW4_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:26:17.723326+00:00
-- url     : https://prove2.me/theorems/2e479e81-38a4-4940-9e4f-ddf79b97f9bf
-- title:
--   Cert: m W4 poly T
-- statement:
--   The fourth test of `mW` is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L190-L193
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L190-L193

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

theorem PaddedDescent.F.Mark.Cert.mW4_polyT {g n y a : α → ℕ} {Ls : α → List Fml} {z : α → List Bool} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls)
    (hy : PolyT y) (ha : PolyT a) (hz : PolyT z) : PolyT fun x => mW4 (g x) (n x) (Ls x) (y x) (a x) (z x) := by sorry
