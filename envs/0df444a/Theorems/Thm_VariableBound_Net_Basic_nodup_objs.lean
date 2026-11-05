-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_nodup_objs
-- name    : VariableBound.Net.Basic.nodup_objs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:43:58.818343+00:00
-- url     : https://prove2.me/theorems/3a0ded1e-997b-4126-8021-057502201fcb
-- title:
--   Basic: nodup objs
-- statement:
--   For well-formed data (WfD), no object occurs twice in the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L92-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L92-L107

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Basic
open Groundwork Groundwork.Prog PaddedDescent.F
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Basic.nodup_objs (hW : WfD k n D) : (objs D).Nodup := by sorry
