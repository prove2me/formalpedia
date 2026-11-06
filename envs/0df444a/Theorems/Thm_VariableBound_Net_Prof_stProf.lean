-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_stProf
-- name    : VariableBound.Net.Prof.stProf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:45.950208+00:00
-- url     : https://prove2.me/theorems/acd195b1-c07e-48e9-b38f-74fa7035e1eb
-- title:
--   Prof: st Prof
-- statement:
--   `StProf`. Step 3, «Profiles»: «every nonzero term belongs to exactly one profile», and that
--   profile is admissible iff |Π₀| = n̄ + 1 (for F: ≤ n̄) and Σ_j |Π_j| ≤ M. In Lean: for g > 0,
--   well-formed data (WfD) and a set P of places of objects, the number of admissible profiles y < `nPr`
--   to which P belongs is 1 if P is within these limits, and 0 otherwise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L363-L374
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L363-L374

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

theorem VariableBound.Net.Prof.stProf : StProf := by sorry
