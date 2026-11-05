-- Prove2me | Theorems.Thm_VariableBound_Net_Rank_tst_comm
-- name    : VariableBound.Net.Rank.tst_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:57:30.729215+00:00
-- url     : https://prove2.me/theorems/9a8f9b43-57cc-47c6-9ea1-8840b49967c6
-- title:
--   Rank: tst comm
-- statement:
--   The objects with the test {a, b} are those with the test {b, a}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L72-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L72-L74

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Rank
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork Groundwork.Prog
open VariableBound.Net.Rank

theorem VariableBound.Net.Rank.tst_comm (g n : ℕ) (D : Dat) (a b κ : ℕ) : tst g n D a b κ = tst g n D b a κ := by sorry
