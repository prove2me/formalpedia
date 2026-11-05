-- Prove2me | Theorems.Thm_Value_stCliqueValueOf
-- name    : Value.stCliqueValueOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:17:13.743766+00:00
-- url     : https://prove2.me/theorems/7fbe52d1-e3d2-422d-a7ec-b46ceec24b49
-- title:
--   Value: st Clique Value Of
-- statement:
--   The value as a sum over one string per edge, from the three statements before it: restrict the
--   sum over the settings to the terms in which all copies agree, and change the variable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Clique.lean#L74-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Clique.lean#L74-L113

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

theorem Value.stCliqueValueOf : StCliqueValueOf := by sorry
