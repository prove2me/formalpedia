-- Prove2me | Theorems.Thm_UniformInK_Correct_kcU_eq
-- name    : UniformInK.Correct.kcU_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:41:57.711361+00:00
-- url     : https://prove2.me/theorems/8bad503b-6df1-4ba2-ba96-5fea0c89d104
-- title:
--   Correct: kc U eq
-- statement:
--   If 2^β ≤ n + 1, the cut-off of the width does nothing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Correct.lean#L26-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/Correct.lean#L26-L29

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
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open UniformInK UniformInK.Correct
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL
open PaddedDescent.F.Mark (WfL occ nSat)

theorem UniformInK.Correct.kcU_eq {k n s : ℕ} (h : 2 ^ betaU k s ≤ n + 1) : kcU k n = k := by sorry
