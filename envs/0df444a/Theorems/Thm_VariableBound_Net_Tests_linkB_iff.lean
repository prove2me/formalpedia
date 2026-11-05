-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_linkB_iff
-- name    : VariableBound.Net.Tests.linkB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:52:55.466365+00:00
-- url     : https://prove2.me/theorems/b1602ec3-8540-45cc-8eff-958908de87f7
-- title:
--   Tests: link B iff
-- statement:
--   a and b are neighbours in the chain of the object e exactly when a < b, e touches both, and e
--   touches no node between them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L36-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L36-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff
import Theorems.Thm_PaddedDescent_F_Mark_Prof_linkB_iff

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Tests.linkB_iff {e a b : ℕ} : linkB g n D e a b = true ↔
    a < b ∧ tchB g n D a e = true ∧ tchB g n D b e = true ∧ ∀ c < g, a < c → c < b → tchB g n D c e = false := by sorry
