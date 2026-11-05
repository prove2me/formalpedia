-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_two_pow_lin_unary
-- name    : PaddedDescent.F.CertTop.two_pow_lin_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:16:05.629522+00:00
-- url     : https://prove2.me/theorems/c4f7397c-9a55-4514-ab93-0ce0021bb70b
-- title:
--   Cert Top: two pow lin unary
-- statement:
--   2^(a·s + c) is given in unary if n is, for s = sOf n and any numbers a and c, since 2^(sOf n) ≤
--   n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L104-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L104-L107

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

theorem PaddedDescent.F.CertTop.two_pow_lin_unary (a c : ℕ) {n : α → ℕ} (hn : Unary n) : Unary fun x => 2 ^ (a * sOf (n x) + c) := by sorry
