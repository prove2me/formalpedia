-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_sqU_polyT
-- name    : PaddedDescent.F.CertTop.sqU_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:39:54.965524+00:00
-- url     : https://prove2.me/theorems/1eb42d97-1158-45bd-b056-0bc4fa32a70c
-- title:
--   Cert Top: sq U poly T
-- statement:
--   g² in unary is polynomial-time in g in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L44-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L44-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_CertSparsify
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_PaddedDescent_F_CertTop
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop
open Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Sparsify
open WidthK (theta)
open WidthK.Prog (stepK)
variable {α : Type} [Enc α]

theorem PaddedDescent.F.CertTop.sqU_polyT {g : α → U} (hg : PolyT g) : PolyT fun x => sqU (g x) := by sorry
