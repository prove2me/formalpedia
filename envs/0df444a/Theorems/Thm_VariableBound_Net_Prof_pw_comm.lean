-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_pw_comm
-- name    : VariableBound.Net.Prof.pw_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:27.759208+00:00
-- url     : https://prove2.me/theorems/d9b051a6-0bd7-4e09-bfcd-2bdd0e543f89
-- title:
--   Prof: pw comm
-- statement:
--   The number of members of P with the test {a, b} does not depend on the order of a and b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L61-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L61-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_PaddedDescent_F_MarkProf
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_VariableBound_Net_Prof
import Theorems.Thm_PaddedDescent_F_Mark_Prof_pw_comm

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.pw_comm (g n : ℕ) (D : Dat) (P : Finset ℕ) (a b κ : ℕ) : pw g n D P a b κ = pw g n D P b a κ := by sorry
