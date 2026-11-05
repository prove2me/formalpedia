-- Prove2me | Theorems.Thm_UniformInK_Correct_brute_eq
-- name    : UniformInK.Correct.brute_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:09.878222+00:00
-- url     : https://prove2.me/theorems/27ee8182-d7b4-4a73-8010-7ae07fdcd6ff
-- title:
--   Correct: brute eq
-- statement:
--   With a pad of at least 2^n units, exhaustive counting on the decoded formula returns the number
--   of satisfying assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Correct.lean#L33-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Correct.lean#L33-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Definitions.Def_UniformInK_Top_Correct
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open UniformInK UniformInK.Correct
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL
open PaddedDescent.F.Mark (WfL occ nSat)

theorem UniformInK.Correct.brute_eq (hBr : StBruteC) (hDU : StDecU) {k n : ℕ} (φ : Sat3.CNF n) (hk : 1 ≤ k) (hφ : SatK.IsKCNF k φ) (w : U) (hw : 2 ^ n ≤ w.length) :
    ((rng w (2 ^ n)).filter fun y => satAt (Decode.toN φ) y).length = SatK.numSat φ := by sorry
