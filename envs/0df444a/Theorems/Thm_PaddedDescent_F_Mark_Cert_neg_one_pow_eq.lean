-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Cert_neg_one_pow_eq
-- name    : PaddedDescent.F.Mark.Cert.neg_one_pow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:18:35.068568+00:00
-- url     : https://prove2.me/theorems/594c9b5f-cd23-459b-ae5d-8d2466b7ba2a
-- title:
--   Cert: neg one pow eq
-- statement:
--   (−1)^k by the parity of k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L121-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertMark.lean#L121-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_PaddedDescent_F_CertMark
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Cert
open Groundwork Groundwork.Prog Groundwork.Grid
variable {α : Type} [Enc α]

theorem PaddedDescent.F.Mark.Cert.neg_one_pow_eq (k : ℕ) : (-1 : ℤ) ^ k = if k % 2 = 0 then 1 else -1 := by sorry
