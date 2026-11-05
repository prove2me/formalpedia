-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_adm_polyT
-- name    : PaddedDescent.F.Mark.Cert.adm_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:26:28.878586+00:00
-- url     : https://prove2.me/theorems/b8f95d28-5875-4970-8d27-1741f62aa48e
-- title:
--   Cert: adm poly T
-- statement:
--   The test «the profile y is admissible» is polynomial-time, with g in unary, for every width k of
--   the clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L238-L241
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L238-L241

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

theorem PaddedDescent.F.Mark.Cert.adm_polyT (k : ℕ) {g n w y : α → ℕ} {Ls : α → List Fml} (hg : Unary g) (hn : PolyT n) (hw : PolyT w) (hL : PolyT Ls)
    (hy : PolyT y) : PolyT fun x => adm k (g x) (n x) (w x) (Ls x) (y x) := by sorry
