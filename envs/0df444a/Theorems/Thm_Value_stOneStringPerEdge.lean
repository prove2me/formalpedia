-- Prove2me | Theorems.Thm_Value_stOneStringPerEdge
-- name    : Value.stOneStringPerEdge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:17:38.620045+00:00
-- url     : https://prove2.me/theorems/9c13edff-e862-418e-836f-ec6594488a36
-- title:
--   Value: st One String Per Edge
-- statement:
--   The choices of settings in which all copies agree are the choices of one string per edge.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Clique.lean#L47-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Clique.lean#L47-L70

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

theorem Value.stOneStringPerEdge : StOneStringPerEdge := by sorry
