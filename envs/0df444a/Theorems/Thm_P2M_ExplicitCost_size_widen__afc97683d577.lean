-- Prove2me | Theorems.Thm_P2M_ExplicitCost_size_widen__afc97683d577
-- name    : P2M_ExplicitCost_size_widen__afc97683d577
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:46:34.620441+00:00
-- url     : https://prove2.me/theorems/c7bcf42f-800a-47a7-a690-962f8fa169e4
-- title:
--   P2 M Explicit Cost size widen  afc97683d577: P2 M Explicit Cost size widen  afc97683d577
-- statement:
--   The widened input of a factor is larger by at most one copy of K and g in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L95-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/SameRuns.lean#L95-L95

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

theorem P2M_ExplicitCost_size_widen__afc97683d577 (u : (X0 NetInput × ℕ) × ℕ) : size (widen₂ K g u) ≤ size u + (2 * K + 2 * g + 2) := by sorry

alias «ExplicitCost».«size_widen₂» := P2M_ExplicitCost_size_widen__afc97683d577
