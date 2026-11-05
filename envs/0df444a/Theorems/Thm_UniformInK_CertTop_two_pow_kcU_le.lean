-- Prove2me | Theorems.Thm_UniformInK_CertTop_two_pow_kcU_le
-- name    : UniformInK.CertTop.two_pow_kcU_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:32.542198+00:00
-- url     : https://prove2.me/theorems/3d80e0e2-911b-46d3-a412-98633cb5b419
-- title:
--   Cert Top: two pow kc U le
-- statement:
--   2 to the width cut off is at most n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Top.lean#L52-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Top.lean#L52-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_UniformInK_Cert_Top
set_option autoImplicit false
section
section
open UniformInK UniformInK.CertTop
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
variable {α : Type} [Enc α]
variable {k K n s D : α → ℕ}

theorem UniformInK.CertTop.two_pow_kcU_le (k n : ℕ) : 2 ^ kcU k n ≤ n + 1 := by sorry
