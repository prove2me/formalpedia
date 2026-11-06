-- Prove2me | Theorems.Thm_VariableBound_Net_SizeB_linkB_iff
-- name    : VariableBound.Net.SizeB.linkB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:47:29.644207+00:00
-- url     : https://prove2.me/theorems/49123ec8-af7f-407d-bf2b-0d5521881a55
-- title:
--   Size B: link B iff
-- statement:
--   {a, b} with a < b is a test of e iff e touches a and b and no node between them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L48-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L48-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeB
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Prof_linkB_iff

set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.SizeB
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat} {y : ℕ}

theorem VariableBound.Net.SizeB.linkB_iff {e a b : ℕ} : linkB g n D e a b = true ↔
    a < b ∧ tchB g n D a e = true ∧ tchB g n D b e = true ∧ ∀ c < g, a < c → c < b → tchB g n D c e = false := by sorry
