-- Prove2me | Theorems.Thm_RecursionToBound_nPrMax_polyT
-- name    : RecursionToBound.nPrMax_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:12:19.595944+00:00
-- url     : https://prove2.me/theorems/4e1d5d95-e480-4753-988e-134a2ff3d23a
-- title:
--   Recursion To Bound: n Pr Max poly T
-- statement:
--   The bound on the number of profiles is polynomial-time if K, n and Δ are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L93-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L93-L95

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

theorem RecursionToBound.nPrMax_polyT {K n Δ : α → ℕ} (hK : Unary K) (hn : Unary n) (hΔ : Unary Δ) : PolyT fun x => nPrMax (K x) (n x) (Δ x) := by sorry
