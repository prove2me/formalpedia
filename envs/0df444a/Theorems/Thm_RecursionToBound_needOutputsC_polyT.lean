-- Prove2me | Theorems.Thm_RecursionToBound_needOutputsC_polyT
-- name    : RecursionToBound.needOutputsC_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:18:15.253031+00:00
-- url     : https://prove2.me/theorems/17769f4e-db4c-4a5c-b317-b63d3d3b7be5
-- title:
--   Recursion To Bound: need Outputs C poly T
-- statement:
--   The maximum over Δ, computed under a bound, is polynomial-time if the solver, the bound, r and
--   the index are and k and n are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L154-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L154-L164

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
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

theorem RecursionToBound.needOutputsC_polyT (hP : S.Poly) {b : α → U} {k n : α → ℕ} {r : α → ℕ × ℕ} {i : α → Idx} (hb : PolyT b) (hk : Unary k) (hr : PolyT r) (hi : PolyT i) (hn : Unary n) :
    PolyT fun x => needOutputsC S (b x) (k x) (r x) (i x) (n x) := by sorry
