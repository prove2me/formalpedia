-- Prove2me | Theorems.Thm_P2M_ExplicitCost_mirrors___7c80e4a094aa
-- name    : P2M_ExplicitCost_mirrors___7c80e4a094aa
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:51:14.659989+00:00
-- url     : https://prove2.me/theorems/9614f530-c09e-4f55-801a-efb0215c1ae9
-- title:
--   P2 M Explicit Cost mirrors   7c80e4a094aa: P2 M Explicit Cost mirrors   7c80e4a094aa
-- statement:
--   Ψ_{a,b}(z, z'): one query, the same with K and g beside the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L76-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L76-L77

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)

theorem P2M_ExplicitCost_mirrors___7c80e4a094aa : Mirrors asked.Ψ askedData.Ψ (Prod.map (widenC K g) id) (2 * K + 2 * g + 2) := by sorry

alias «ExplicitCost».«mirrors_Ψ» := P2M_ExplicitCost_mirrors___7c80e4a094aa
