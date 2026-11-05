-- Prove2me | Theorems.Thm_VariableBound_Net_Rank_mu_comm
-- name    : VariableBound.Net.Rank.mu_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:57:39.901054+00:00
-- url     : https://prove2.me/theorems/f561b866-b9db-42e3-82d3-18701da0f86c
-- title:
--   Rank: mu comm
-- statement:
--   μ_(a,b,κ) = μ_(b,a,κ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L77-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L77-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Rank
import Theorems.Thm_PaddedDescent_F_Mark_Prof_mu_comm

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
open Groundwork Groundwork.Prog
open VariableBound.Net.Rank

theorem VariableBound.Net.Rank.mu_comm (g : ℕ) (D : Dat) (y a b κ : ℕ) : mu g D y a b κ = mu g D y b a κ := by sorry
