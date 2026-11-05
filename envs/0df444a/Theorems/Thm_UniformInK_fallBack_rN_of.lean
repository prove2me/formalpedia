-- Prove2me | Theorems.Thm_UniformInK_fallBack_rN_of
-- name    : UniformInK.fallBack_rN_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:17.400203+00:00
-- url     : https://prove2.me/theorems/8fabb4d7-eeff-450c-9814-f9f8df90654c
-- title:
--   Uniform In K: fall Back r N of
-- statement:
--   The rate log₂ log₂(n+4)/(log₂(n+4))^α, α ≤ 1, allows the fall-back to exhaustive counting.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/FallBack.lean#L59-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/FallBack.lean#L59-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_UniformInK_Top_FallBack
set_option autoImplicit false
section
section
open UniformInK
open ClauseBound.TopN.GenN UniformInK.FallBack

theorem UniformInK.fallBack_rN_of {α : ℝ} (ha1 : α ≤ 1) : FallBack (SatK.rN 1 α) := by sorry
