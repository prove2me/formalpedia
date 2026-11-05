-- Prove2me | Theorems.Thm_VariableBound_Correct_planAtD_some
-- name    : VariableBound.Correct.planAtD_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:06.975524+00:00
-- url     : https://prove2.me/theorems/1b7a34ff-f3a6-454a-90c4-d5ec1e4d0e83
-- title:
--   Correct: plan At D some
-- statement:
--   What a plan says, for a polynomial-time solver: the three tests hold, and the exponent is
--   `needD`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/Correct.lean#L24-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/Correct.lean#L24-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open VariableBound VariableBound.Correct
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.Net

theorem VariableBound.Correct.planAtD_some {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) {k n s v : ℕ} {i : Idx} (h : planAtD S k n i s = some v) :
    (s0U k ≤ s ∧ 2 ^ betaU k s ≤ n + 1 ∧ 29 * LD (2 ^ betaU k s) + 19 ≤ n) ∧ v = needD S k i n s := by sorry
