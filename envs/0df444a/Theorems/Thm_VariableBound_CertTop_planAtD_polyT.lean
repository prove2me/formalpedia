-- Prove2me | Theorems.Thm_VariableBound_CertTop_planAtD_polyT
-- name    : VariableBound.CertTop.planAtD_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:06:48.840248+00:00
-- url     : https://prove2.me/theorems/0cabcda9-4189-4da7-a22d-40c0ec43a779
-- title:
--   Cert Top: plan At D poly T
-- statement:
--   The plan is polynomial-time if the solver is, k, n and s are given in unary and the index is
--   polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Cert/Top.lean#L103-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Cert/Top.lean#L103-L129

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
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

theorem VariableBound.CertTop.planAtD_polyT (hP : S.Poly) {k n s : α → ℕ} {i : α → Idx} (hk : Unary k) (hn : Unary n) (hi : PolyT i) (hs : Unary s) :
    PolyT fun x => planAtD S (k x) (n x) (i x) (s x) := by sorry
