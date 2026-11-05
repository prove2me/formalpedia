-- Prove2me | Theorems.Thm_SparsificationLemma_Geo_stThrGeo
-- name    : SparsificationLemma.Geo.stThrGeo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T00:06:51.594981+00:00
-- url     : https://prove2.me/theorems/79ff1ba7-bf77-4c22-9357-bba989463dbb
-- title:
--   Geo: st Thr Geo
-- statement:
--   The thresholds `thetaU τ` with the numbers `betaSU τ` satisfy the four conditions, if 1 ≤ k and
--   8k ≤ τ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Thr.lean#L27-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/Thr.lean#L27-L27

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

theorem SparsificationLemma.Geo.stThrGeo : StThrGeo := by sorry
