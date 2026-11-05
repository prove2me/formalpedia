-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_div_qv_lt
-- name    : VariableBound.Net.Basic.div_qv_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:18:52.13256+00:00
-- url     : https://prove2.me/theorems/e4e6e15a-1fa5-4788-84f1-59d5038715ad
-- title:
--   Basic: div qv lt
-- statement:
--   For g > 0, the node that holds the variable x < n is below g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L156-L167
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L156-L167

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Basic
open Groundwork Groundwork.Prog PaddedDescent.F
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Basic.div_qv_lt (hg : 0 < g) {x : ℕ} (hx : x < n) : x / qv g n < g := by sorry
