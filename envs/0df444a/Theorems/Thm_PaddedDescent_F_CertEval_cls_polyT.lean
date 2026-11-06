-- Prove2me | Theorems.Thm_PaddedDescent_F_CertEval_cls_polyT
-- name    : PaddedDescent.F.CertEval.cls_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:31:11.487202+00:00
-- url     : https://prove2.me/theorems/e4c78a4a-cfbc-4df1-9f4e-ef5f9f74f43f
-- title:
--   Cert Eval: cls poly T
-- statement:
--   The list of all clauses with the index of their layer is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertEval.lean#L51-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertEval.lean#L51-L52

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

theorem PaddedDescent.F.CertEval.cls_polyT {Ls : α → List Fml} (hL : PolyT Ls) : PolyT fun x => cls (Ls x) := by sorry
