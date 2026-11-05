-- Prove2me | Theorems.Thm_VariableBound_Net_Rank_count_false_cons
-- name    : VariableBound.Net.Rank.count_false_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:58:19.361939+00:00
-- url     : https://prove2.me/theorems/e2924455-fdd4-4831-b052-0bceaf081609
-- title:
--   Rank: count false cons
-- statement:
--   A bit 0 in front does not change the number of ones.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L31-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Rank
import Theorems.Thm_Groundwork_PolyT_count
attribute [local fun_prop] Groundwork.PolyT.count


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork Groundwork.Prog
open VariableBound.Net.Rank

theorem VariableBound.Net.Rank.count_false_cons (x : List Bool) : (false :: x).count true = x.count true := by sorry
