-- Prove2me | Theorems.Thm_UniformInK_ifaceU
-- name    : UniformInK.ifaceU
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:51:47.045229+00:00
-- url     : https://prove2.me/theorems/00570508-a0c0-4725-a18a-94c9912a5072
-- title:
--   Uniform In K: iface U
-- statement:
--   `StIfaceU` from the statements on nodes and on thresholds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Iface.lean#L28-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Iface.lean#L28-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_UniformInK_Spars_Iface
set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK WidthK.Prog WidthK.ProgMain

theorem UniformInK.ifaceU (h1 : StNodeRootU) (h2 : StNodeStepU) (h3 : StNodeBoundU) (h8 : StThrU) (h9 : StBetaSumU) : StIfaceU := by sorry
