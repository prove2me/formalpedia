-- Prove2me | Theorems.Thm_VariableBound_Net_Prof_tgt_place
-- name    : VariableBound.Net.Prof.tgt_place
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:45:37.404594+00:00
-- url     : https://prove2.me/theorems/1a73e707-ebdf-460a-971d-e017b855a6aa
-- title:
--   Prof: tgt place
-- statement:
--   The digit of P at the place (a·g + b)·2 + κ, for b < g and κ < 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L303-L307
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Prof.lean#L303-L307

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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_tgt_place

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Prof
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

theorem VariableBound.Net.Prof.tgt_place {g n : ℕ} {D : Dat} (P : Finset ℕ) {a b κ : ℕ} (hb : b < g) (hκ : κ < 2) :
    tgt g n D P ((a * g + b) * 2 + κ) = if b < a then 0 else if a = b then oc g n D P a κ else pw g n D P a b κ := by sorry
