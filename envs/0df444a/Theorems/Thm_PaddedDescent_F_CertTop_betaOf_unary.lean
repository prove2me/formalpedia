-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_betaOf_unary
-- name    : PaddedDescent.F.CertTop.betaOf_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:40:27.454197+00:00
-- url     : https://prove2.me/theorems/aac3d659-ebcd-42f5-bed2-c3204078841d
-- title:
--   Cert Top: beta Of unary
-- statement:
--   The logarithm of the length of a block of the code is given in unary if n is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L119-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L119-L120

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

theorem PaddedDescent.F.CertTop.betaOf_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => betaOf (sOf (n x)) := by sorry
