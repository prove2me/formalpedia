-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_exists_tch
-- name    : VariableBound.Net.Basic.exists_tch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:58:23.991744+00:00
-- url     : https://prove2.me/theorems/b95d3b6a-aa57-4912-a79b-72651fbd0612
-- title:
--   Basic: exists tch
-- statement:
--   For g > 0 and well-formed data (WfD), every object touches a node below g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L176-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L176-L178

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Basic
open Groundwork Groundwork.Prog PaddedDescent.F
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Basic.exists_tch (hg : 0 < g) (hW : WfD k n D) {o : ℕ} (ho : o < (objs D).length) : ∃ a < g, tchB g n D a o = true := by sorry
