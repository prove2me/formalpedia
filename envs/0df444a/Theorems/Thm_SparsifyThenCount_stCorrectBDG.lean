-- Prove2me | Theorems.Thm_SparsifyThenCount_stCorrectBDG
-- name    : SparsifyThenCount.stCorrectBDG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:17.45803+00:00
-- url     : https://prove2.me/theorems/e4c5ef3f-4d75-4149-aaec-9e6e30118ed1
-- title:
--   Sparsify Then Count: st Correct BDG
-- statement:
--   The merged function, run with thresholds that serve, is right on every k-CNF, for every k ≥ 1
--   and every n, when the pad has length at least 2^(eBD …); given that the two algorithms are right
--   (`StCorrectDG`, `StCorrectM`), the test on the
--   variables (`UniformInK.StAllOccU`) and the decoder (`StDecM`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CorrectB.lean#L31-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/CorrectB.lean#L31-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_VariableBound_Top_CorrectB
import Definitions.Def_SparsifyThenCount_CorrectB
set_option autoImplicit false
section
section
open SparsifyThenCount
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound VariableBound.CorrectB

theorem SparsifyThenCount.stCorrectBDG (h : StCorrectDG) (hM : StCorrectM) (hA : StAllOccU) (hD : StDecM) : StCorrectBDG := by sorry
