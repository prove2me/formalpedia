-- Prove2me | Theorems.Thm_SplitSat_decides_mono
-- name    : SplitSat.decides_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:34:16.245261+00:00
-- url     : https://prove2.me/theorems/2a085775-002a-4052-8f43-b8cd3460a58d
-- title:
--   Split Sat: decides mono
-- statement:
--   `Decides M k δ c` stays true when δ and c are made larger.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Simulate.lean#L35-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Simulate.lean#L35-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_SplitSat_Simulate
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Paper CountKSat Eight.ViaGrouping

theorem SplitSat.decides_mono {M : StepMachine (List Bool) Bool} {k : ℕ} {δ δ' : ℝ} {c c' : ℕ} (hδ : δ ≤ δ') (hc : c ≤ c') (h : Decides M k δ c) :
    Decides M k δ' c' := by sorry
