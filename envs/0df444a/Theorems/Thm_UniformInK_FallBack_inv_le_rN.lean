-- Prove2me | Theorems.Thm_UniformInK_FallBack_inv_le_rN
-- name    : UniformInK.FallBack.inv_le_rN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:10.079272+00:00
-- url     : https://prove2.me/theorems/e0f3dae2-2cda-4686-9303-09800534e8cb
-- title:
--   Fall Back: inv le r N
-- statement:
--   The rate is at least 1/log₂(n+4).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/FallBack.lean#L41-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Top/FallBack.lean#L41-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_TopN_Gen
import Definitions.Def_UniformInK_Top_FallBack
set_option autoImplicit false
section
section
open UniformInK UniformInK.FallBack
open ClauseBound.TopN.GenN

theorem UniformInK.FallBack.inv_le_rN {α : ℝ} (ha1 : α ≤ 1) (n : ℕ) : 1 / Real.logb 2 ((n : ℝ) + 4) ≤ SatK.rN 1 α n := by sorry
