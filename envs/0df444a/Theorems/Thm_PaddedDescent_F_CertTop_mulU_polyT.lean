-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_mulU_polyT
-- name    : PaddedDescent.F.CertTop.mulU_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:40:40.123359+00:00
-- url     : https://prove2.me/theorems/3dcee7fc-73c4-44a5-ad46-d17ae86aa221
-- title:
--   Cert Top: mul U poly T
-- statement:
--   K·L in unary is polynomial-time in K and L in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L40-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L40-L41

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

theorem PaddedDescent.F.CertTop.mulU_polyT {K L : α → U} (hK : PolyT K) (hL : PolyT L) : PolyT fun x => mulU (K x) (L x) := by sorry
