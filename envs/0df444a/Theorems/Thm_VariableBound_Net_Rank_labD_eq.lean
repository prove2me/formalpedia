-- Prove2me | Theorems.Thm_VariableBound_Net_Rank_labD_eq
-- name    : VariableBound.Net.Rank.labD_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:33.065291+00:00
-- url     : https://prove2.me/theorems/ad83ebc9-c562-4fce-902d-46ffc02f4d6b
-- title:
--   Rank: lab D eq
-- statement:
--   The label is the word of kind 0 followed by the word of kind 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L86-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Rank.lean#L86-L89

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

theorem VariableBound.Net.Rank.labD_eq (g n : ℕ) (D : Dat) (y a b : ℕ) (z : List Bool) :
    labD g n D y a b z = toWord (cw (tst g n D a b 0).length (mu g D y a b 0)) (rank (str g n D a b 0 z))
      ++ toWord (cw (tst g n D a b 1).length (mu g D y a b 1)) (rank (str g n D a b 1 z)) := by sorry
