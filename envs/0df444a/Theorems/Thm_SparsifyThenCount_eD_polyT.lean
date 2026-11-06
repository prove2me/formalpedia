-- Prove2me | Theorems.Thm_SparsifyThenCount_eD_polyT
-- name    : SparsifyThenCount.eD_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:12:05.941351+00:00
-- url     : https://prove2.me/theorems/24ef40db-8a6f-48bc-974c-35fe2941cf82
-- title:
--   Sparsify Then Count: e D poly T
-- statement:
--   The exponent function of the input for the bound in n is polynomial-time, if the solver, `pick`
--   and `slU` are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CertTop.lean#L46-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CertTop.lean#L46-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_VariableBound_Cert_Top
import Definitions.Def_UniformInK_Cert_Top
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_SparsifyThenCount_CertTop
set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.CertTop SparsificationLemma

theorem SparsifyThenCount.eD_polyT {Idx : Type} [Enc Idx] (S : Solver Idx) (hP : S.Poly) {pick : U → U × Idx} {slU : U → U} (hpick : PolyT pick) (hsl : PolyT slU) :
    PolyT (eD S pick slU) := by sorry
