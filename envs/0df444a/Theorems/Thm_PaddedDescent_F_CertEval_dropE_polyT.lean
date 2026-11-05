-- Prove2me | Theorems.Thm_PaddedDescent_F_CertEval_dropE_polyT
-- name    : PaddedDescent.F.CertEval.dropE_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:17:41.124371+00:00
-- url     : https://prove2.me/theorems/1b3bf151-1f83-4748-919d-b882ff5b0e36
-- title:
--   Cert Eval: drop E poly T
-- statement:
--   The test that puts a clause into layer i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertEval.lean#L80-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertEval.lean#L80-L90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertTop
import Definitions.Def_PaddedDescent_F_CertEval
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval
open Groundwork Groundwork.Prog
open PaddedDescent.F.Mark (Cl cls nProf adm markF dropE placeAt placeE)
variable {α : Type} [Enc α]
variable {ev : α → List Fml → ℤ} {w : α → ℕ} {Ls : α → List Fml} {C : α → Cl}

theorem PaddedDescent.F.CertEval.dropE_polyT (hev : PolyT fun q : α × List Fml => ev q.1 q.2) (hw : Unary w) (hL : PolyT Ls) (hC : PolyT C) {i : α → ℕ}
    (hi : PolyT i) : PolyT fun x => dropE (ev x) (w x) (Ls x) (C x) (i x) := by sorry
