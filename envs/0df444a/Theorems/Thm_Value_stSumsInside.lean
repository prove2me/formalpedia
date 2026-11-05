-- Prove2me | Theorems.Thm_Value_stSumsInside
-- name    : Value.stSumsInside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:23:36.139774+00:00
-- url     : https://prove2.me/theorems/640f58dc-617d-4536-a4d1-a39d15cb588f
-- title:
--   Value: st Sums Inside
-- statement:
--   «Together with the sums inside the tables»: every node lies in exactly one group, so a family
--   (z_γ)_γ of settings of the groups is one choice z of a setting for every node.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Sums.lean#L31-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Sums.lean#L31-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Sums
set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Finset Eight.SecNetworks

theorem Value.stSumsInside : StSumsInside := by sorry
