-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_stNPr
-- name    : VariableBound.Net.Prof.stNPr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:46:08.437197+00:00
-- url     : https://prove2.me/theorems/cd8f37d7-771d-4a26-9136-faf196acc875
-- title:
--   Prof: st NPr
-- statement:
--   `StNPr`. Step 3, «Profiles»: «of which there are at most (I + m + 1)^(2(g² + g))»: the number
--   `nPr` of the numbers y that are tried as profiles, the admissible ones among them, is at most this;
--   and I + m ≤ r·s + m. Needs that every check has at most s clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L392-L398
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L392-L398

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
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.stNPr : StNPr := by sorry
