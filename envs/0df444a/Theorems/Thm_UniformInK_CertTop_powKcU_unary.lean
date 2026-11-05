-- Prove2me | Theorems.Thm_UniformInK_CertTop_powKcU_unary
-- name    : UniformInK.CertTop.powKcU_unary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T01:58:03.23841+00:00
-- url     : https://prove2.me/theorems/e9378dd1-965c-4890-940d-0351d5a1dc05
-- title:
--   Cert Top: pow Kc U unary
-- statement:
--   2 to the width cut off is given in unary if k and n are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Top.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Cert/Top.lean#L56-L57

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

theorem UniformInK.CertTop.powKcU_unary (hk : Unary k) (hn : Unary n) : Unary fun x => 2 ^ kcU (k x) (n x) := by sorry
