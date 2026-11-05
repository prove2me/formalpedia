-- Prove2me | Theorems.Thm_UniformInK_End_one_le_length
-- name    : UniformInK.End.one_le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:46:22.008262+00:00
-- url     : https://prove2.me/theorems/78b55b5f-58c9-4793-a1c2-d12deb84d80a
-- title:
--   End: one le length
-- statement:
--   If every variable occurs and there is a variable, there is a clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/End.lean#L45-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/End.lean#L45-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_UniformInK_Top_End
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open UniformInK UniformInK.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End

theorem UniformInK.End.one_le_length {n : ℕ} {φ : Sat3.CNF n} (hn : 1 ≤ n) (ho : SatM.AllOccur φ) : 1 ≤ φ.length := by sorry
