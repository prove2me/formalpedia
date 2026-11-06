-- Prove2me | Theorems.Thm_VariableBound_CertTop_restD_polyT
-- name    : VariableBound.CertTop.restD_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:10:10.109563+00:00
-- url     : https://prove2.me/theorems/5eb792b4-d623-4f5d-a990-49b7845c56f9
-- title:
--   Cert Top: rest D poly T
-- statement:
--   The exponent for everything but the networks is polynomial-time if k, K, n and s are given in
--   unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Cert/Top.lean#L54-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Cert/Top.lean#L54-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Cert_Top
import Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_LD_polyT
import Theorems.Thm_ClauseBound_TopN_Cert_lamS_unary

set_option autoImplicit false
section
section
open VariableBound VariableBound.CertTop
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound.Net VariableBound.Net.CertEv
open ClauseBound.TopN.Cert (lamS_unary)
open ClauseBound.ParityChecks.CertTopOL (LD_polyT)
variable {α : Type} [Enc α]
variable {k K n s : α → ℕ}

theorem VariableBound.CertTop.restD_polyT (hk : Unary k) (hK : Unary K) (hn : Unary n) (hs : Unary s) : PolyT fun x => restD (k x) (K x) (n x) (s x) := by sorry
