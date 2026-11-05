-- Prove2me | Theorems.Thm_UniformInK_CertTop_blockU_unary
-- name    : UniformInK.CertTop.blockU_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:53:09.900454+00:00
-- url     : https://prove2.me/theorems/1948fdb6-c622-4f55-be92-1dab807bee63
-- title:
--   Cert Top: block U unary
-- statement:
--   2^β cut off at n + 1 is given in unary if k, n and s are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Top.lean#L43-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Top.lean#L43-L45

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

theorem UniformInK.CertTop.blockU_unary (hk : Unary k) (hn : Unary n) (hs : Unary s) : Unary fun x => blockU (k x) (n x) (s x) := by sorry
