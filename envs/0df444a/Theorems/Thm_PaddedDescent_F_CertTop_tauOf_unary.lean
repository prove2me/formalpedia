-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_tauOf_unary
-- name    : PaddedDescent.F.CertTop.tauOf_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:39:50.645587+00:00
-- url     : https://prove2.me/theorems/14eab4c5-6c02-4a1f-8cbd-332748121d5a
-- title:
--   Cert Top: tau Of unary
-- statement:
--   The threshold τ of the sparsification is given in unary if n is, since 2^(sOf n) ≤ n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L110-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L110-L112

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

theorem PaddedDescent.F.CertTop.tauOf_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => tauOf (sOf (n x)) := by sorry
