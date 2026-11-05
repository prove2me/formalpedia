-- Prove2me | Theorems.Thm_VariableBound_Net_Rank_length_str
-- name    : VariableBound.Net.Rank.length_str
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:53.93537+00:00
-- url     : https://prove2.me/theorems/db18e53a-3f5f-493f-9585-de018815dbdf
-- title:
--   Rank: length str
-- statement:
--   The string of marks has one bit for each object with the test.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L82-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L82-L83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Rank
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork Groundwork.Prog
open VariableBound.Net.Rank

theorem VariableBound.Net.Rank.length_str (g n : ℕ) (D : Dat) (a b κ : ℕ) (z : List Bool) : (str g n D a b κ z).length = (tst g n D a b κ).length := by sorry
