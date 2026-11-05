-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_tch_polyT
-- name    : PaddedDescent.F.Mark.Cert.tch_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:21:35.858865+00:00
-- url     : https://prove2.me/theorems/54c588f3-bab5-44d0-b711-bc394860a61e
-- title:
--   Cert: tch poly T
-- statement:
--   The list of the clauses that touch a node.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L50-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L50-L52

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

theorem PaddedDescent.F.Mark.Cert.tch_polyT {g n a : α → ℕ} {Ls : α → List Fml} (hg : PolyT g) (hn : PolyT n) (hL : PolyT Ls) (ha : PolyT a) :
    PolyT fun x => tch (g x) (n x) (Ls x) (a x) := by sorry
