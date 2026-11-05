-- Prove2me | Theorems.Thm_VariableBound_Net_Rank_rank_inj
-- name    : VariableBound.Net.Rank.rank_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:45.676818+00:00
-- url     : https://prove2.me/theorems/2015ae1a-c44c-42a7-a894-00f53c63adc2
-- title:
--   Rank: rank inj
-- statement:
--   Two strings of the same length with as many ones and the same position are equal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L50-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L50-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Rank
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork Groundwork.Prog
open VariableBound.Net.Rank

theorem VariableBound.Net.Rank.rank_inj (x x' : List Bool) (hl : x.length = x'.length) (hc : x.count true = x'.count true) (hr : rank x = rank x') : x = x' := by sorry
