-- Prove2me | Theorems.Thm_RecursionToBound_needAtC_polyT
-- name    : RecursionToBound.needAtC_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:12:28.44934+00:00
-- url     : https://prove2.me/theorems/1ce3c11a-a0b6-4892-aa3c-d6b591e3440d
-- title:
--   Recursion To Bound: need At C poly T
-- statement:
--   The exponent for one Δ, computed under a bound, is polynomial-time if the solver, the bound and
--   the index are and k, n and Δ are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L102-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L102-L113

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

theorem RecursionToBound.needAtC_polyT (hP : S.Poly) {b : α → U} {k n Δ : α → ℕ} {i : α → Idx} (hb : PolyT b) (hk : Unary k) (hi : PolyT i) (hn : Unary n) (hΔ : Unary Δ) :
    PolyT fun x => needAtC S (b x) (k x) (i x) (n x) (Δ x) := by sorry
