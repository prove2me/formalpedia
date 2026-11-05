-- Prove2me | Theorems.Thm_VariableBound_Net_Rank_toWord_rank_inj
-- name    : VariableBound.Net.Rank.toWord_rank_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:43:25.505236+00:00
-- url     : https://prove2.me/theorems/4ef7254b-220c-4225-9adf-3fa8dc5da131
-- title:
--   Rank: to Word rank inj
-- statement:
--   The words of ⌈log C(t, μ)⌉ bits of the positions of two strings of t bits with μ ones agree if
--   and only if the strings agree.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L98-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L98-L103

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

theorem VariableBound.Net.Rank.toWord_rank_inj (x x' : List Bool) (t μ : ℕ) (ht : x.length = t) (ht' : x'.length = t) (hμ : x.count true = μ) (hμ' : x'.count true = μ) :
    toWord (cw t μ) (rank x) = toWord (cw t μ) (rank x') ↔ x = x' := by sorry
