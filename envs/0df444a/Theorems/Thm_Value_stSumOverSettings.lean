-- Prove2me | Theorems.Thm_Value_stSumOverSettings
-- name    : Value.stSumOverSettings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:16:15.484324+00:00
-- url     : https://prove2.me/theorems/33756294-8000-47cc-a35d-5b681cdd1a35
-- title:
--   Value: st Sum Over Settings
-- statement:
--   The value of a (K, λ)-clique is by definition a sum over the settings of its nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Clique.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Clique.lean#L31-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_Value_Clique
set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Finset Eight.SecNetworks

theorem Value.stSumOverSettings : StSumOverSettings := by sorry
