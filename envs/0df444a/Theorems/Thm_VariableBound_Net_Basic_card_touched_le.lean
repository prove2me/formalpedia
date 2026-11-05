-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_card_touched_le
-- name    : VariableBound.Net.Basic.card_touched_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:58:15.027852+00:00
-- url     : https://prove2.me/theorems/10feac58-0dea-4798-ab92-c602fa0a2da8
-- title:
--   Basic: card touched le
-- statement:
--   The object o touches at most (number of literals of its clause) + (kind of o) nodes below g.
--   With at most k literals (WfD) this gives the bound «at most k − 1 + κ tests» of Appendix D, Step 3
--   of the paper, which is not stated here.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L183-L200
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L183-L200

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Basic
open Groundwork Groundwork.Prog PaddedDescent.F
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Basic.card_touched_le (o : ℕ) : ((Finset.range g).filter fun a => tchB g n D a o = true).card ≤ (clOf D o).length + (obAt D o).1 := by sorry
