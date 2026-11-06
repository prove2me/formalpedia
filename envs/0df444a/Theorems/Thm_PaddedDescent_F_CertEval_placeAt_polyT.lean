-- Prove2me | Theorems.Thm_PaddedDescent_F_CertEval_placeAt_polyT
-- name    : PaddedDescent.F.CertEval.placeAt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:18:11.266615+00:00
-- url     : https://prove2.me/theorems/cf3ff5da-d0a5-4229-be4a-4ab748d2fd51
-- title:
--   Cert Eval: place At poly T
-- statement:
--   A clause added to layer i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertEval.lean#L93-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertEval.lean#L93-L94

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

theorem PaddedDescent.F.CertEval.placeAt_polyT (hL : PolyT Ls) (hC : PolyT C) {i : α → ℕ} (hi : PolyT i) : PolyT fun x => placeAt (Ls x) (C x) (i x) := by sorry
