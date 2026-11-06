-- Prove2me | Theorems.Thm_SparsifyThenCount_planD_polyT
-- name    : SparsifyThenCount.planD_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:12:02.148758+00:00
-- url     : https://prove2.me/theorems/db3a9f90-d93d-4efa-8e10-b90f23de6c3e
-- title:
--   Sparsify Then Count: plan D poly T
-- statement:
--   The plan, as a function of the input, is polynomial-time, if the solver, `pick` and `slU` are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CertTop.lean#L36-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CertTop.lean#L36-L42

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

theorem SparsifyThenCount.planD_polyT {Idx : Type} [Enc Idx] (S : Solver Idx) (hP : S.Poly) {pick : U → U × Idx} {slU : U → U} (hpick : PolyT pick) (hsl : PolyT slU) :
    PolyT (planD S pick slU) := by sorry
