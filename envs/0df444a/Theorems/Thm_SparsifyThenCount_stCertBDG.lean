-- Prove2me | Theorems.Thm_SparsifyThenCount_stCertBDG
-- name    : SparsifyThenCount.stCertBDG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:18:21.657165+00:00
-- url     : https://prove2.me/theorems/ab20806e-978c-416c-a115-d0789f18f3ca
-- title:
--   Sparsify Then Count: st Cert BDG
-- statement:
--   For thresholds that serve, the merged function of (input, pad) and its exponent function of the
--   input are polynomial-time if the solver, `pick` and `slU` are; given that the algorithm for the
--   bound in n is (`StCertDG`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CertBoth.lean#L56-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CertBoth.lean#L56-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_SparsifyThenCount_CertTop
import Definitions.Def_UniformInK_Cert_Both
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_SparsifyThenCount_CertBoth
set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.CertBoth VariableBound

theorem SparsifyThenCount.stCertBDG (h : StCertDG) : StCertBDG := by sorry
