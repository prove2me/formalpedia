-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_capOf_unary
-- name    : PaddedDescent.F.CertTop.capOf_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:40:47.727307+00:00
-- url     : https://prove2.me/theorems/a940d312-dd38-4f66-b4d3-b4ae775c7829
-- title:
--   Cert Top: cap Of unary
-- statement:
--   The cap of the cut-off sums is given in unary if n is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L115-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L115-L116

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

theorem PaddedDescent.F.CertTop.capOf_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => capOf (n x) := by sorry
