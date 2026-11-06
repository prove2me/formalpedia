-- Prove2me | Theorems.Thm_VariableBound_Net_SizeB_own_or_test
-- name    : VariableBound.Net.SizeB.own_or_test
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:47:40.246125+00:00
-- url     : https://prove2.me/theorems/3dbfbb9d-f494-4e87-8fb5-efb32daf4cab
-- title:
--   Size B: own or test
-- statement:
--   Step 3, «The parameters»: an object that touches the node a is owned by a or has a test {c, a}
--   with a node c < a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L110-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeB.lean#L110-L123

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
set_option autoImplicit false
section
open VariableBound VariableBound.Net VariableBound.Net.SizeB
open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat} {y : ℕ}

theorem VariableBound.Net.SizeB.own_or_test {a o : ℕ} (h : tchB g n D a o = true) : ownB g n D o a = true ∨ ∃ c < a, linkB g n D o c a = true := by sorry
