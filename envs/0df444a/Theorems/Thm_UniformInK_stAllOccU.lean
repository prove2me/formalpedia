-- Prove2me | Theorems.Thm_UniformInK_stAllOccU
-- name    : UniformInK.stAllOccU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:06:04.33362+00:00
-- url     : https://prove2.me/theorems/81cd2031-3829-4cf0-b5d6-c801f839c096
-- title:
--   Uniform In K: st All Occ U
-- statement:
--   On the code of an instance the test says whether every variable occurs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/CorrectB.lean#L27-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/CorrectB.lean#L27-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_UniformInK_Top_CorrectB
set_option autoImplicit false
section
section
open UniformInK
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK.CorrectB

theorem UniformInK.stAllOccU (hD : StDecM) : StAllOccU := by sorry
