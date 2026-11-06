-- Prove2me | Theorems.Thm_SparsifyThenCount_useMD_polyT
-- name    : SparsifyThenCount.useMD_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:17:23.043009+00:00
-- url     : https://prove2.me/theorems/eaac67d8-ac1b-4ee7-9391-8d360547dcd2
-- title:
--   Sparsify Then Count: use MD poly T
-- statement:
--   The test that chooses the algorithm for the bound in m is polynomial-time, if the solver, `pick`
--   and `slU` are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CertBoth.lean#L33-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CertBoth.lean#L33-L45

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

theorem SparsifyThenCount.useMD_polyT {Idx : Type} [Enc Idx] (S : Solver Idx) (hS : S.Poly) {pick : U → U × Idx} {slU : U → U} (hpick : PolyT pick) (hsl : PolyT slU) :
    PolyT (useMD S pick slU) := by sorry
