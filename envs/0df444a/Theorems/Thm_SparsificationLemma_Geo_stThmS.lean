-- Prove2me | Theorems.Thm_SparsificationLemma_Geo_stThmS
-- name    : SparsificationLemma.Geo.stThmS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:02:17.516888+00:00
-- url     : https://prove2.me/theorems/d982e5e0-06be-4cea-aa5e-6cb8571cfded
-- title:
--   Geo: st Thm S
-- statement:
--   The theorem for τ = 2^(4s+17) and s ≥ `s0U k`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/S.lean#L25-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Geo/S.lean#L25-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Geo_Tau
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_SparsificationLemma_Geo_S
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Geo
open Finset Groundwork Groundwork.Sparsify CountKSat UniformInK PaddedDescent

theorem SparsificationLemma.Geo.stThmS : StThmS := by sorry
