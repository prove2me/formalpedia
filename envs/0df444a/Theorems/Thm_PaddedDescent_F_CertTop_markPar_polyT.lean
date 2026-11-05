-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_markPar_polyT
-- name    : PaddedDescent.F.CertTop.markPar_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:17:58.411878+00:00
-- url     : https://prove2.me/theorems/25d04679-3574-41b6-9ff2-77acac3e70fb
-- title:
--   Cert Top: mark Par poly T
-- statement:
--   The parameters of the evaluations are polynomial-time in n in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L160-L161
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L160-L161

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

theorem PaddedDescent.F.CertTop.markPar_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun x => markPar (n x) (sOf (n x)) := by sorry
