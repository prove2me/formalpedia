-- Prove2me | Theorems.Thm_P2M_ExplicitCost_size_widen__a57a929d61ba
-- name    : P2M_ExplicitCost_size_widen__a57a929d61ba
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:48:58.462896+00:00
-- url     : https://prove2.me/theorems/ee7f30dc-fb66-4a52-84c8-90761de40c49
-- title:
--   P2 M Explicit Cost size widen  a57a929d61ba: P2 M Explicit Cost size widen  a57a929d61ba
-- statement:
--   The widened input of a term is larger by at most one copy of K and g in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L92-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L92-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)

theorem P2M_ExplicitCost_size_widen__a57a929d61ba (u : X0 NetInput × ℕ) : size (widen₁ K g u) ≤ size u + (2 * K + 2 * g + 2) := by sorry

alias «ExplicitCost».«size_widen₁» := P2M_ExplicitCost_size_widen__a57a929d61ba
