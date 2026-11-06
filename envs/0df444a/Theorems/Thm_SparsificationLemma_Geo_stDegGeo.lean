-- Prove2me | Theorems.Thm_SparsificationLemma_Geo_stDegGeo
-- name    : SparsificationLemma.Geo.stDegGeo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:45.928395+00:00
-- url     : https://prove2.me/theorems/2d02f67e-b540-4ac8-8107-09689aab0be1
-- title:
--   Geo: st Deg Geo
-- statement:
--   2·(θ 0 + … + θ (k−1)) + 2 ≤ τ^(2k), if 1 ≤ k and 8 ≤ τ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Thr.lean#L30-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Thr.lean#L30-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Bound
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_SparsificationLemma_Geo_Thr
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Geo
open Finset UniformInK

theorem SparsificationLemma.Geo.stDegGeo : StDegGeo := by sorry
