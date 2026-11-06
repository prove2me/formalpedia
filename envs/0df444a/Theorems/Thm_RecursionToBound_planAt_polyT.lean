-- Prove2me | Theorems.Thm_RecursionToBound_planAt_polyT
-- name    : RecursionToBound.planAt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:15:18.915074+00:00
-- url     : https://prove2.me/theorems/d0952bd2-8b7a-455a-8824-88a9e25f0a6b
-- title:
--   Recursion To Bound: plan At poly T
-- statement:
--   The plan is polynomial-time if the solver, the index and r are and k and n are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L169-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Cert/Exponent.lean#L169-L179

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

theorem RecursionToBound.planAt_polyT (hP : S.Poly) (n₁ : ℕ) {k n : α → ℕ} {i : α → Idx} {r : α → ℕ × ℕ} (hk : Unary k) (hn : Unary n) (hi : PolyT i) (hr : PolyT r) :
    PolyT fun x => planAt S n₁ (k x) (n x) (i x) (r x) := by sorry
