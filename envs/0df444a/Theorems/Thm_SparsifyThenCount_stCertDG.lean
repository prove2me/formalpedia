-- Prove2me | Theorems.Thm_SparsifyThenCount_stCertDG
-- name    : SparsifyThenCount.stCertDG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:11:18.795193+00:00
-- url     : https://prove2.me/theorems/5a566b77-6d2c-4839-8851-9f88507a7ca4
-- title:
--   Sparsify Then Count: st Cert DG
-- statement:
--   For thresholds that serve, the function `ADG Θ` of (input, pad) is polynomial-time if the
--   solver, `pick` and `slU` are; given the certificates of the walk (`StepSparsify.StCertWalkSG`), of
--   the deletion of the clauses that contain a variable
--   together with its negation (`StepSparsify.StCertNoTaut`) and of the count of one sparse formula by
--   Steps 1 to 4 (`VariableBound.StCertCountD`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CertTop.lean#L57-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CertTop.lean#L57-L102

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

theorem SparsifyThenCount.stCertDG (hW : StepSparsify.StCertWalkSG) (hN : StepSparsify.StCertNoTaut) (hC : StCertCountD) : StCertDG := by sorry
