-- Prove2me | Theorems.Thm_UniformInK_stIfaceU
-- name    : UniformInK.stIfaceU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:52:12.114802+00:00
-- url     : https://prove2.me/theorems/f9baf0df-0cb3-4bfa-bb9a-e53683289595
-- title:
--   Uniform In K: st Iface U
-- statement:
--   All that the walk of the tree needs to know about the rule on finite sets holds for the
--   thresholds `thetaU τ`, if 1 ≤ k and 8k ≤ τ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Main.lean#L25-L25
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Main.lean#L25-L25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_UniformInK_Spars_Step
import Definitions.Def_UniformInK_Spars_Bound
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_UniformInK_Spars_Iface
import Definitions.Def_UniformInK_Spars_Main
set_option autoImplicit false
section
section
open UniformInK

theorem UniformInK.stIfaceU : StIfaceU := by sorry
