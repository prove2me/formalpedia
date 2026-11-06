-- Prove2me | Theorems.Thm_RecursionToBound_stackLen_polyT
-- name    : RecursionToBound.stackLen_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:13:39.406245+00:00
-- url     : https://prove2.me/theorems/1b7d52d3-3baa-4b5f-89d6-0383385ea981
-- title:
--   Recursion To Bound: stack Len poly T
-- statement:
--   The bound on the length of the walk's state is polynomial-time jointly in k, τ and n, if k is
--   given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L64-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L64-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Thresholds
import Definitions.Def_VariableBound_Cert_Top
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_PaddedDescent_F_CertEval
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_RecursionToBound_Cert_Exponent
set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma
variable {α : Type} [Enc α]

theorem RecursionToBound.stackLen_polyT {k τ n : α → ℕ} (hk : Unary k) (hτ : PolyT τ) (hn : PolyT n) : PolyT fun x => stackLenCU (k x) (τ x) (n x) (inLen (k x) (n x)) := by sorry
