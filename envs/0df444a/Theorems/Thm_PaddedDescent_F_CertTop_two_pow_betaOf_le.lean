-- Prove2me | Theorems.Thm_PaddedDescent_F_CertTop_two_pow_betaOf_le
-- name    : PaddedDescent.F.CertTop.two_pow_betaOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:12.615921+00:00
-- url     : https://prove2.me/theorems/e1daee94-eba3-4d6c-bd72-e01ed0cb4568
-- title:
--   Cert Top: two pow beta Of le
-- statement:
--   2^(betaOf (sOf n)) is at most n + 2^49. For sOf n = 0 it is 2^49. For s = sOf n ≥ 1 the
--   logarithm of the logarithm of n is at least 2s + 6, so that
--   betaOf s = (s + 7)² ≤ 2^(2s + 6) is at most the logarithm of n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L130-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertTop.lean#L130-L153

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

theorem PaddedDescent.F.CertTop.two_pow_betaOf_le (n : ℕ) : 2 ^ betaOf (sOf n) ≤ n + 2 ^ 49 := by sorry
