-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_tst_polyT
-- name    : PaddedDescent.F.Mark.Cert.tst_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:22:41.17505+00:00
-- url     : https://prove2.me/theorems/9f86d31f-c1e3-4396-ad7b-90aae31ef3ab
-- title:
--   Cert: tst poly T
-- statement:
--   The list of the clauses of a layer whose marks two nodes compare.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L69-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L69-L71

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

theorem PaddedDescent.F.Mark.Cert.tst_polyT {g n a b i : α → ℕ} {Ls : α → List Fml} (hg : Unary g) (hn : PolyT n) (hL : PolyT Ls)
    (ha : PolyT a) (hb : PolyT b) (hi : PolyT i) : PolyT fun x => tst (g x) (n x) (Ls x) (a x) (b x) (i x) := by sorry
