-- Prove2me | Theorems.Thm_VariableBound_CertTop_needNetC_polyT
-- name    : VariableBound.CertTop.needNetC_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:06:17.704728+00:00
-- url     : https://prove2.me/theorems/b0573db2-9720-4d95-b047-159154dbfef8
-- title:
--   Cert Top: need Net C poly T
-- statement:
--   The exponent of the networks, computed under a bound, is polynomial-time if the solver, the
--   bound and the index are and U, P and B are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Cert/Top.lean#L78-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Cert/Top.lean#L78-L99

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
import Theorems.Thm_ClauseBound_TopN_Cert_needNetC_polyT

set_option autoImplicit false
section
section
open VariableBound VariableBound.CertTop
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound.Net VariableBound.Net.CertEv
open ClauseBound.TopN.Cert (lamS_unary)
open ClauseBound.ParityChecks.CertTopOL (LD_polyT)
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

theorem VariableBound.CertTop.needNetC_polyT (hP : S.Poly) {b : α → U} {i : α → Idx} {Ub P B : α → ℕ} (hb : PolyT b) (hi : PolyT i) (hU : Unary Ub) (hQ : Unary P) (hB : Unary B) :
    PolyT fun x => needNetC S (b x) (i x) (Ub x) (P x) (B x) := by sorry
