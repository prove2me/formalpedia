-- Prove2me | Theorems.Thm_VariableBound_Net_Rank_rank_lt
-- name    : VariableBound.Net.Rank.rank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:53:00.487773+00:00
-- url     : https://prove2.me/theorems/fff1e63c-1b24-4625-9f31-0cefd0a30910
-- title:
--   Rank: rank lt
-- statement:
--   The position of a string is below the number C(t, μ) of strings of its length t with as many
--   ones, μ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L35-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L35-L47

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

theorem VariableBound.Net.Rank.rank_lt (x : List Bool) : rank x < x.length.choose (x.count true) := by sorry
